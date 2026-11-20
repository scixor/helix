//! Portable low-level / systems-programming helpers for Helix:
//! 1. Godbolt-style linked source <-> assembly split highlighting (`; path:line` / `# path:line`)
//! 2. Assembly jump-target & label highlighting (`L0:` <-> `jne L0`, `.LBB...`)
//! 3. `perf annotate --stdio` sample-percentage heat tinting
//! 4. `:inspect-num` (`:num`) integer / bitfield / IEEE-754 float popup

use std::collections::HashSet;
use std::path::Path;

use helix_core::command_line::Args;
use helix_core::RopeSlice;
use helix_view::graphics::Rect;
use helix_view::info::Info;
use helix_view::theme::{Modifier, Style, Theme};
use helix_view::{Document, Editor, View};

use crate::compositor;
use crate::ui::document::{LinePos, TextRenderer};
use crate::ui::text_decorations::DecorationManager;
use crate::ui::PromptEvent;

/// Attach low-level line decorations (linked source<->asm, jump targets, perf heat).
pub fn add_decorations<'d>(
    editor: &Editor,
    doc: &Document,
    view: &View,
    inner: Rect,
    theme: &Theme,
    is_focused: bool,
    decorations: &mut DecorationManager<'d>,
) {
    let text = doc.text().slice(..);
    let total_lines = text.len_lines();
    if total_lines == 0 {
        return;
    }

    let doc_is_asm = is_asm_doc(doc);

    // 1. Linked source <-> asm split highlighting (cross-view sync with the focused pane)
    if !is_focused {
        if let Some(focused_view) = editor.tree.try_get(editor.tree.focus) {
            if let Some(focused_doc) = editor.document(focused_view.doc) {
                let focused_text = focused_doc.text().slice(..);
                let focused_head = focused_doc
                    .selection(focused_view.id)
                    .primary()
                    .cursor(focused_text);
                let focused_line = focused_text.char_to_line(focused_head);
                let focused_is_asm = is_asm_doc(focused_doc);

                if focused_is_asm && !doc_is_asm {
                    // Focused = asm, this pane = source -> highlight target source line
                    if let Some((src_path, target_line_1based)) =
                        nearest_source_loc(focused_text, focused_line)
                    {
                        if path_matches_doc(doc, &src_path) && target_line_1based > 0 {
                            let target_line = target_line_1based - 1;
                            let style = linked_highlight_style(theme);
                            decorations.add_decoration(move |renderer: &mut TextRenderer, pos: LinePos| {
                                if pos.doc_line == target_line {
                                    renderer.set_style(
                                        Rect::new(inner.x, pos.visual_line, inner.width, 1),
                                        style,
                                    );
                                }
                            });
                        }
                    }
                } else if !focused_is_asm && doc_is_asm {
                    // Focused = source, this pane = asm -> highlight all asm lines for focused line
                    if let Some(focused_path) = focused_doc.path() {
                        let target_line_1based = focused_line + 1;
                        let matched = collect_matching_asm_lines(text, focused_path, target_line_1based);
                        if !matched.is_empty() {
                            let style = linked_highlight_style(theme);
                            decorations.add_decoration(move |renderer: &mut TextRenderer, pos: LinePos| {
                                if matched.contains(&pos.doc_line) {
                                    renderer.set_style(
                                        Rect::new(inner.x, pos.visual_line, inner.width, 1),
                                        style,
                                    );
                                }
                            });
                        }
                    }
                }
            }
        }
    }

    // 2. Jump-target & label highlighting inside focused asm buffers
    if is_focused && doc_is_asm {
        let cursor = doc.selection(view.id).primary().cursor(text);
        let cur_line = text.char_to_line(cursor);
        if let Some(label) = extract_cursor_label(text.line(cur_line)) {
            let view_offset = doc.view_offset(view.id);
            let first_line = text.char_to_line(view_offset.anchor.min(text.len_chars()));
            let end_line = (first_line + inner.height as usize + 8).min(total_lines);

            let mut matched = HashSet::new();
            for line_idx in first_line..end_line {
                if line_idx == cur_line {
                    continue;
                }
                if line_matches_label(text.line(line_idx), &label) {
                    matched.insert(line_idx);
                }
            }
            if !matched.is_empty() {
                let style = linked_highlight_style(theme);
                decorations.add_decoration(move |renderer: &mut TextRenderer, pos: LinePos| {
                    if matched.contains(&pos.doc_line) {
                        renderer.set_style(
                            Rect::new(inner.x, pos.visual_line, inner.width, 1),
                            style,
                        );
                    }
                });
            }
        }
    }

    // 3. `perf annotate --stdio` sample-percentage heat tinting
    if doc_is_asm || is_perf_doc(doc) {
        let view_offset = doc.view_offset(view.id);
        let first_line = text.char_to_line(view_offset.anchor.min(text.len_chars()));
        let end_line = (first_line + inner.height as usize + 8).min(total_lines);

        let mut hot_lines: Vec<(usize, u8)> = Vec::new();
        for line_idx in first_line..end_line {
            if let Some(pct) = parse_perf_percent(text.line(line_idx)) {
                if pct >= 10.0 {
                    hot_lines.push((line_idx, 2));
                } else if pct >= 2.0 {
                    hot_lines.push((line_idx, 1));
                }
            }
        }
        if !hot_lines.is_empty() {
            let hot_style = perf_heat_style(theme, true);
            let warm_style = perf_heat_style(theme, false);
            decorations.add_decoration(move |renderer: &mut TextRenderer, pos: LinePos| {
                if let Ok(idx) = hot_lines.binary_search_by_key(&pos.doc_line, |&(l, _)| l) {
                    let style = if hot_lines[idx].1 >= 2 {
                        hot_style
                    } else {
                        warm_style
                    };
                    renderer.set_style(Rect::new(inner.x, pos.visual_line, inner.width, 1), style);
                }
            });
        }
    }
}

/// `:inspect-num` (`:num`) — show integer, bitfield, and IEEE-754 breakdown in an info popup.
pub fn inspect_number(
    cx: &mut compositor::Context,
    args: Args,
    event: PromptEvent,
) -> anyhow::Result<()> {
    if event != PromptEvent::Validate {
        return Ok(());
    }

    let raw = if let Some(arg) = args.first() {
        arg.to_string()
    } else {
        let (view, doc) = current_ref!(cx.editor);
        let text = doc.text().slice(..);
        let sel = doc.selection(view.id).primary();
        let selected = sel.fragment(text).to_string();
        if selected.trim().len() > 1 {
            selected.trim().to_string()
        } else {
            extract_number_token(text, sel.cursor(text))
        }
    };

    let cleaned = raw.trim().trim_matches(|c: char| matches!(c, ',' | ';' | ')' | '(' | '[' | ']'));
    if cleaned.is_empty() {
        cx.editor.set_error("inspect-num: no numeric token under cursor");
        return Ok(());
    }

    let Some(rows) = format_number_rows(cleaned) else {
        cx.editor
            .set_error(format!("inspect-num: could not parse '{cleaned}' as int or float"));
        return Ok(());
    };

    cx.editor.autoinfo = Some(Info::new(format!("Number Inspector: {cleaned}"), &rows));
    Ok(())
}

fn linked_highlight_style(theme: &Theme) -> Style {
    let frameline = theme.get("ui.highlight.frameline");
    if frameline != Style::default() {
        frameline
    } else {
        theme
            .get("ui.cursorline.secondary")
            .add_modifier(Modifier::BOLD)
    }
}

fn perf_heat_style(theme: &Theme, very_hot: bool) -> Style {
    let base = if very_hot {
        theme.get("diff.minus")
    } else {
        theme.get("diff.delta")
    };
    let bg = base.bg.or(theme.get("ui.cursorline.secondary").bg);
    let mut style = Style::default();
    if let Some(bg) = bg {
        style = style.bg(bg);
    }
    if very_hot {
        style = style.add_modifier(Modifier::BOLD);
    }
    style
}

fn is_asm_doc(doc: &Document) -> bool {
    if let Some(name) = doc.language_name() {
        if matches!(name, "nasm" | "gas" | "asm") {
            return true;
        }
    }
    if let Some(ext) = doc.path().and_then(|p| p.extension()).and_then(|e| e.to_str()) {
        return matches!(ext, "asm" | "s" | "S" | "nasm");
    }
    false
}

fn is_perf_doc(doc: &Document) -> bool {
    doc.path()
        .and_then(|p| p.file_name())
        .and_then(|n| n.to_str())
        .is_some_and(|n| n.contains("perf"))
}

/// Parse a source-location comment like `; src/foo.zig:121` or `# /abs/foo.c:42:10`.
fn parse_source_loc_comment(line: RopeSlice<'_>) -> Option<(String, usize)> {
    let s = line.to_string();
    let trimmed = s.trim();
    let rest = trimmed
        .strip_prefix(';')
        .or_else(|| trimmed.strip_prefix('#'))?
        .trim();
    // Must contain a file path with an extension + `:line` (avoid `; src: ...` prose)
    if rest.is_empty() || rest.contains(' ') {
        return None;
    }
    let mut parts = rest.rsplitn(3, ':');
    let last = parts.next()?;
    let prev = parts.next()?;
    // Handle `path:line` or `path:line:col`
    let (path, line_str) = if let Ok(_col) = last.parse::<usize>() {
        if let Ok(_line) = prev.parse::<usize>() {
            (parts.next()?, prev)
        } else {
            (prev, last)
        }
    } else {
        return None;
    };
    let line_num: usize = line_str.parse().ok()?;
    if line_num == 0 || path.is_empty() || !path.contains('.') {
        return None;
    }
    Some((path.to_string(), line_num))
}

fn nearest_source_loc(text: RopeSlice<'_>, from_line: usize) -> Option<(String, usize)> {
    let start = from_line.min(text.len_lines().saturating_sub(1));
    for line_idx in (0..=start).rev() {
        let line = text.line(line_idx);
        if let Some(loc) = parse_source_loc_comment(line) {
            return Some(loc);
        }
        // Stop scanning if we cross into a previous function header
        if line_idx < start && is_function_label(line) {
            break;
        }
    }
    None
}

fn collect_matching_asm_lines(
    text: RopeSlice<'_>,
    source_path: &Path,
    target_line_1based: usize,
) -> HashSet<usize> {
    let mut matched = HashSet::new();
    let mut active_match = false;
    let total = text.len_lines().min(20_000);

    for line_idx in 0..total {
        let line = text.line(line_idx);
        if let Some((comment_path, comment_line)) = parse_source_loc_comment(line) {
            active_match = comment_line == target_line_1based
                && path_suffix_matches(source_path, &comment_path);
            continue;
        }
        if !active_match {
            continue;
        }
        let s = line.to_string();
        let trimmed = s.trim();
        if trimmed.is_empty() || trimmed.starts_with(';') || trimmed.starts_with('#') {
            continue;
        }
        if trimmed.ends_with(':') {
            if is_function_label(line) {
                active_match = false;
            }
            continue;
        }
        matched.insert(line_idx);
    }
    matched
}

fn path_matches_doc(doc: &Document, comment_path: &str) -> bool {
    let Some(doc_path) = doc.path() else {
        return false;
    };
    path_suffix_matches(doc_path, comment_path)
}

fn path_suffix_matches(full: &Path, candidate: &str) -> bool {
    let cand = Path::new(candidate);
    if full == cand || full.ends_with(cand) {
        return true;
    }
    if cand.is_absolute() {
        return cand.ends_with(full);
    }
    false
}

fn is_function_label(line: RopeSlice<'_>) -> bool {
    let s = line.to_string();
    let t = s.trim();
    if !t.ends_with(':') || t.starts_with(';') || t.starts_with('#') {
        return false;
    }
    let name = &t[..t.len() - 1];
    // Local labels look like `L0`, `.LBB...`, `.L...`
    if name.starts_with('.') {
        return false;
    }
    if let Some(rest) = name.strip_prefix('L') {
        if !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit()) {
            return false;
        }
    }
    !name.is_empty() && !name.contains(' ')
}

fn extract_cursor_label(line: RopeSlice<'_>) -> Option<String> {
    let s = line.to_string();
    let code = s.split(';').next().unwrap_or("").trim();
    if code.is_empty() {
        return None;
    }
    // Label definition: `L0:` or `.LBB280_1:`
    if let Some(lbl) = code.strip_suffix(':') {
        let lbl = lbl.trim_matches(|c| c == '<' || c == '>');
        if is_valid_label_token(lbl) {
            return Some(lbl.to_string());
        }
        return None;
    }
    // Branch instruction: `jne L6`, `jb .LBB280_1`, `jmp <L0>`
    let mut parts = code.split_whitespace();
    let mnem = parts.next()?;
    if mnem.starts_with('j') || mnem == "loop" || mnem == "loope" || mnem == "loopne" {
        let target = parts.next()?.trim_matches(|c| c == '<' || c == '>');
        if is_valid_label_token(target) {
            return Some(target.to_string());
        }
    }
    None
}

fn line_matches_label(line: RopeSlice<'_>, label: &str) -> bool {
    let s = line.to_string();
    let code = s.split(';').next().unwrap_or("").trim();
    if let Some(def) = code.strip_suffix(':') {
        return def.trim_matches(|c| c == '<' || c == '>') == label;
    }
    let mut parts = code.split_whitespace();
    let Some(mnem) = parts.next() else {
        return false;
    };
    if mnem.starts_with('j') || mnem == "loop" || mnem == "loope" || mnem == "loopne" {
        if let Some(target) = parts.next() {
            return target.trim_matches(|c| c == '<' || c == '>') == label;
        }
    }
    false
}

fn is_valid_label_token(s: &str) -> bool {
    !s.is_empty()
        && s.bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'$'))
}

fn parse_perf_percent(line: RopeSlice<'_>) -> Option<f32> {
    let s = line.to_string();
    let trimmed = s.trim_start();
    let colon = trimmed.find(':')?;
    if colon == 0 || colon > 10 {
        return None;
    }
    let num_str = trimmed[..colon].trim();
    if !num_str.contains('.') {
        return None;
    }
    num_str.parse::<f32>().ok()
}

fn extract_number_token(text: RopeSlice<'_>, cursor: usize) -> String {
    let len = text.len_chars();
    if len == 0 {
        return String::new();
    }
    let pos = cursor.min(len.saturating_sub(1));
    let is_num_char = |c: char| {
        c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '+' | '-')
    };
    let mut start = pos;
    while start > 0 && is_num_char(text.char(start - 1)) {
        let prev = text.char(start - 1);
        // Only include `+`/`-` if exponent sign or leading sign
        if matches!(prev, '+' | '-') {
            let before = if start >= 2 {
                Some(text.char(start - 2))
            } else {
                None
            };
            if !matches!(before, Some('e' | 'E' | 'p' | 'P') | None)
                && !before.is_some_and(|c| !c.is_ascii_alphanumeric() && c != '_')
            {
                break;
            }
        }
        start -= 1;
    }
    let mut end = pos;
    while end < len && is_num_char(text.char(end)) {
        let cur = text.char(end);
        if matches!(cur, '+' | '-') && end > start {
            let prev = text.char(end - 1);
            if !matches!(prev, 'e' | 'E' | 'p' | 'P') {
                break;
            }
        }
        end += 1;
    }
    text.slice(start..end).to_string()
}

fn format_number_rows(raw: &str) -> Option<Vec<(&'static str, String)>> {
    let s = raw.replace('_', "");
    let (neg, body) = if let Some(rest) = s.strip_prefix('-') {
        (true, rest)
    } else if let Some(rest) = s.strip_prefix('+') {
        (false, rest)
    } else {
        (false, s.as_str())
    };

    // Integer parse: 0x / 0b / 0o / decimal
    let parsed_u64: Option<u64> = if let Some(hex) = body
        .strip_prefix("0x")
        .or_else(|| body.strip_prefix("0X"))
    {
        u64::from_str_radix(hex, 16).ok()
    } else if let Some(bin) = body
        .strip_prefix("0b")
        .or_else(|| body.strip_prefix("0B"))
    {
        u64::from_str_radix(bin, 2).ok()
    } else if let Some(oct) = body
        .strip_prefix("0o")
        .or_else(|| body.strip_prefix("0O"))
    {
        u64::from_str_radix(oct, 8).ok()
    } else if body.chars().all(|c| c.is_ascii_digit()) && !body.is_empty() {
        body.parse::<u64>().ok()
    } else {
        None
    };

    if let Some(mag) = parsed_u64 {
        let bits: u64 = if neg { mag.wrapping_neg() } else { mag };
        let signed = bits as i64;
        let mut rows = vec![
            ("u64", format!("{bits}")),
            ("i64", format!("{signed}")),
            ("hex", format!("0x{bits:X}  (0x{bits:016x})")),
            ("oct", format!("0o{bits:o}")),
            ("bin", format_grouped_bin(bits)),
            ("bits", format_set_bits(bits)),
        ];
        if bits <= u32::MAX as u64 {
            let f = f32::from_bits(bits as u32);
            rows.push(("as f32", format_f32_fields(f)));
        }
        let d = f64::from_bits(bits);
        rows.push(("as f64", format_f64_fields(d)));
        return Some(rows);
    }

    // Float parse
    if let Ok(d) = s.parse::<f64>() {
        let f = d as f32;
        return Some(vec![
            ("f64", format_f64_fields(d)),
            ("f64 bits", format!("0x{:016x}", d.to_bits())),
            ("f32", format_f32_fields(f)),
            ("f32 bits", format!("0x{:08x}", f.to_bits())),
        ]);
    }

    None
}

fn format_grouped_bin(v: u64) -> String {
    let width = if v == 0 {
        8
    } else {
        let used = 64 - v.leading_zeros() as usize;
        used.div_ceil(4) * 4
    };
    let mut out = String::from("0b");
    for bit in (0..width).rev() {
        if bit + 1 != width && (bit + 1) % 4 == 0 {
            out.push('_');
        }
        out.push(if (v >> bit) & 1 != 0 { '1' } else { '0' });
    }
    out
}

fn format_set_bits(v: u64) -> String {
    let pop = v.count_ones();
    if pop == 0 {
        return "none (popcnt=0)".to_string();
    }
    let mut indices = Vec::with_capacity(pop as usize);
    for b in 0..64u32 {
        if (v >> b) & 1 != 0 {
            indices.push(b.to_string());
        }
    }
    format!("[{}] (popcnt={pop})", indices.join(", "))
}

fn format_f32_fields(f: f32) -> String {
    let bits = f.to_bits();
    let sign = bits >> 31;
    let exp = (bits >> 23) & 0xff;
    let mant = bits & 0x7f_ffff;
    let unbiased = (exp as i32) - 127;
    format!("{f:e}  | s={sign} exp={exp} (2^{unbiased}) mant=0x{mant:06x}")
}

fn format_f64_fields(d: f64) -> String {
    let bits = d.to_bits();
    let sign = bits >> 63;
    let exp = (bits >> 52) & 0x7ff;
    let mant = bits & 0xf_ffff_ffff_ffff;
    let unbiased = (exp as i32) - 1023;
    format!("{d:e}  | s={sign} exp={exp} (2^{unbiased}) mant=0x{mant:013x}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use helix_core::Rope;

    #[test]
    fn parses_source_loc_comments() {
        let r = Rope::from("; src/manifold/brep/brep_reader.zig:121\n");
        assert_eq!(
            parse_source_loc_comment(r.line(0)),
            Some(("src/manifold/brep/brep_reader.zig".into(), 121))
        );
        let r2 = Rope::from("# /abs/path/foo.c:42:8\n");
        assert_eq!(
            parse_source_loc_comment(r2.line(0)),
            Some(("/abs/path/foo.c".into(), 42))
        );
        let r3 = Rope::from("; regular comment with spaces: 12\n");
        assert_eq!(parse_source_loc_comment(r3.line(0)), None);
    }

    #[test]
    fn extracts_labels_and_jumps() {
        assert_eq!(
            extract_cursor_label(Rope::from("L6:\n").line(0)),
            Some("L6".into())
        );
        assert_eq!(
            extract_cursor_label(Rope::from("    jne       L6 ; <-- loop back\n").line(0)),
            Some("L6".into())
        );
        assert!(line_matches_label(Rope::from("    je .LBB280_1\n").line(0), ".LBB280_1"));
    }

    #[test]
    fn parses_numbers() {
        assert!(format_number_rows("0x3f80_0000").is_some());
        assert!(format_number_rows("0b1011_0100").is_some());
        assert!(format_number_rows("1e-7").is_some());
        assert!(format_number_rows("-42").is_some());
    }
}
