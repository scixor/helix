//! Portable low-level / systems-programming helpers for Helix:
//! 1. 3-way Godbolt-style linked Source <-> Assembly <-> llvm-mca split highlighting & auto-scroll
//! 2. Assembly jump-target & label highlighting + `gd` jump-to-label (x86-64 & ARM64)
//! 3. `llvm-mca` + `perf annotate --stdio` syntax highlight overlays & perf heat tinting
//! 4. `:mca [mcpu]` live `llvm-mca` analysis on any visual selection or enclosing asm function
//! 5. `:inspect-num` (`:num`) integer / bitfield / IEEE-754 float popup
//! 6. Smart `gf` path[:line[:col]] jump with workspace suffix resolution + picker

use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::ops::Range;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;

use helix_core::command_line::Args;
use helix_core::syntax::{Highlight, OverlayHighlights};
use helix_core::{RopeSlice, Selection, Tendril, Transaction};
use helix_view::editor::Action;
use helix_view::graphics::{Color, Rect};
use helix_view::info::Info;
use helix_view::theme::{Modifier, Style, Theme};
use helix_view::view::ViewPosition;
use helix_view::{Document, DocumentId, Editor, View, ViewId};

use crate::commands;
use crate::compositor;
use crate::job::Callback;
use crate::ui::document::{LinePos, TextRenderer};
use crate::ui::overlay::overlaid;
use crate::ui::picker::{Column as PickerColumn, PathOrId, Picker};
use crate::ui::text_decorations::DecorationManager;
use crate::ui::PromptEvent;

static LAST_SYNC_CURSOR: Mutex<Option<(ViewId, usize)>> = Mutex::new(None);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DocKind {
    Source,
    Asm,
    Mca,
}

fn classify_doc(doc: &Document) -> DocKind {
    if is_mca_doc(doc) {
        DocKind::Mca
    } else if is_asm_doc(doc) {
        DocKind::Asm
    } else {
        DocKind::Source
    }
}

/// Auto-scroll unfocused linked Source <-> Asm <-> MCA splits when the focused cursor moves.
pub fn sync_linked_views(editor: &mut Editor) {
    let focused_id = editor.tree.focus;
    let Some(focused_view) = editor.tree.try_get(focused_id) else {
        return;
    };
    let Some(focused_doc) = editor.document(focused_view.doc) else {
        return;
    };
    let focused_text = focused_doc.text().slice(..);
    if focused_text.len_lines() == 0 {
        return;
    }
    let focused_head = focused_doc
        .selection(focused_view.id)
        .primary()
        .cursor(focused_text);
    let focused_line = focused_text.char_to_line(focused_head);

    {
        let mut last = LAST_SYNC_CURSOR.lock().unwrap();
        if *last == Some((focused_id, focused_line)) {
            return;
        }
        *last = Some((focused_id, focused_line));
    }

    let focused_kind = classify_doc(focused_doc);
    let mut scroll_targets: Vec<(ViewId, DocumentId, usize, usize)> = Vec::new();

    match focused_kind {
        DocKind::Asm => {
            // Asm -> Source
            if let Some((src_path, target_line_1based)) =
                nearest_source_loc(focused_text, focused_line)
            {
                if target_line_1based > 0 {
                    let target_line = target_line_1based - 1;
                    for (view, is_focused) in editor.tree.views() {
                        if is_focused {
                            continue;
                        }
                        let Some(doc) = editor.document(view.doc) else {
                            continue;
                        };
                        if classify_doc(doc) == DocKind::Source && path_matches_doc(doc, &src_path) {
                            let height = view.inner_area(doc).height as usize;
                            scroll_targets.push((view.id, doc.id(), target_line, height));
                        }
                    }
                }
            }
            // Asm -> MCA
            for (view, is_focused) in editor.tree.views() {
                if is_focused {
                    continue;
                }
                let Some(doc) = editor.document(view.doc) else {
                    continue;
                };
                if classify_doc(doc) == DocKind::Mca {
                    let mca_text = doc.text().slice(..);
                    if let Some(insn_idx) = asm_line_to_mca_index(focused_text, focused_line, mca_text) {
                        if let Some(mca_line) = find_mca_line_for_index(mca_text, insn_idx) {
                            let height = view.inner_area(doc).height as usize;
                            scroll_targets.push((view.id, doc.id(), mca_line, height));
                        }
                    }
                }
            }
        }
        DocKind::Source => {
            if let Some(focused_path) = focused_doc.path() {
                let target_line_1based = focused_line + 1;
                let mut first_asm_match: Option<(DocumentId, usize)> = None;
                for (view, is_focused) in editor.tree.views() {
                    if is_focused {
                        continue;
                    }
                    let Some(doc) = editor.document(view.doc) else {
                        continue;
                    };
                    if classify_doc(doc) == DocKind::Asm {
                        let matched = collect_matching_asm_lines(
                            doc.text().slice(..),
                            focused_path,
                            target_line_1based,
                        );
                        if let Some(&first_asm_line) = matched.iter().min() {
                            if first_asm_match.is_none() {
                                first_asm_match = Some((doc.id(), first_asm_line));
                            }
                            let height = view.inner_area(doc).height as usize;
                            scroll_targets.push((view.id, doc.id(), first_asm_line, height));
                        }
                    }
                }
                // Source -> Asm -> MCA chain
                if let Some((asm_doc_id, asm_line)) = first_asm_match {
                    if let Some(asm_doc) = editor.document(asm_doc_id) {
                        let asm_text = asm_doc.text().slice(..);
                        for (view, is_focused) in editor.tree.views() {
                            if is_focused {
                                continue;
                            }
                            let Some(doc) = editor.document(view.doc) else {
                                continue;
                            };
                            if classify_doc(doc) == DocKind::Mca {
                                let mca_text = doc.text().slice(..);
                                if let Some(insn_idx) =
                                    asm_line_to_mca_index(asm_text, asm_line, mca_text)
                                {
                                    if let Some(mca_line) = find_mca_line_for_index(mca_text, insn_idx)
                                    {
                                        let height = view.inner_area(doc).height as usize;
                                        scroll_targets.push((view.id, doc.id(), mca_line, height));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        DocKind::Mca => {
            // MCA -> Asm -> Source chain
            if let Some(mca_ref) = parse_mca_line_insn_ref(focused_text, focused_line) {
                let mut matched_source: Option<(String, usize)> = None;
                for (view, is_focused) in editor.tree.views() {
                    if is_focused {
                        continue;
                    }
                    let Some(doc) = editor.document(view.doc) else {
                        continue;
                    };
                    if classify_doc(doc) == DocKind::Asm {
                        let asm_text = doc.text().slice(..);
                        if let Some(asm_line) =
                            resolve_mca_ref_to_asm_line(asm_text, focused_text, &mca_ref)
                        {
                            let height = view.inner_area(doc).height as usize;
                            scroll_targets.push((view.id, doc.id(), asm_line, height));
                            if matched_source.is_none() {
                                matched_source = nearest_source_loc(asm_text, asm_line);
                            }
                        }
                    }
                }
                if let Some((src_path, target_line_1based)) = matched_source {
                    if target_line_1based > 0 {
                        let target_line = target_line_1based - 1;
                        for (view, is_focused) in editor.tree.views() {
                            if is_focused {
                                continue;
                            }
                            let Some(doc) = editor.document(view.doc) else {
                                continue;
                            };
                            if classify_doc(doc) == DocKind::Source
                                && path_matches_doc(doc, &src_path)
                            {
                                let height = view.inner_area(doc).height as usize;
                                scroll_targets.push((view.id, doc.id(), target_line, height));
                            }
                        }
                    }
                }
            }
        }
    }

    for (view_id, doc_id, target_line, height) in scroll_targets {
        let Some(doc) = editor.document_mut(doc_id) else {
            continue;
        };
        let text = doc.text().slice(..);
        let total = text.len_lines();
        if total == 0 || target_line >= total {
            continue;
        }
        let cur_offset = doc.view_offset(view_id);
        let top_line = text.char_to_line(cur_offset.anchor.min(text.len_chars()));
        let margin = (height / 6).clamp(1, 4);
        let in_comfort_zone = target_line >= top_line + margin
            && target_line + margin < top_line + height.max(1);
        if in_comfort_zone {
            continue;
        }
        let new_top = target_line.saturating_sub(height / 2);
        let anchor = text.line_to_char(new_top.min(total - 1));
        doc.set_view_offset(
            view_id,
            ViewPosition {
                anchor,
                horizontal_offset: 0,
                vertical_offset: 0,
            },
        );
    }
}

/// Attach low-level line decorations (3-way linked Source<->Asm<->MCA, critical path, jump labels, perf heat).
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

    let doc_kind = classify_doc(doc);

    // 0. If this is an asm pane and ANY open split is an MCA buffer, mark MCA critical-path lines
    if doc_kind == DocKind::Asm {
        if let Some(mca_doc) = find_open_doc_of_kind(editor, DocKind::Mca) {
            let mca_text = mca_doc.text().slice(..);
            let crit_indices = collect_mca_critical_indices(mca_text);
            if !crit_indices.is_empty() {
                let crit_lines = map_mca_indices_to_asm_lines(text, mca_text, &crit_indices);
                if !crit_lines.is_empty() {
                    let style = critical_path_style(theme);
                    decorations.add_decoration(move |renderer: &mut TextRenderer, pos: LinePos| {
                        if crit_lines.contains(&pos.doc_line) {
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

    // 1. 3-way linked Source <-> Asm <-> MCA split highlighting
    if !is_focused {
        if let Some(focused_view) = editor.tree.try_get(editor.tree.focus) {
            if let Some(focused_doc) = editor.document(focused_view.doc) {
                let focused_text = focused_doc.text().slice(..);
                let focused_head = focused_doc
                    .selection(focused_view.id)
                    .primary()
                    .cursor(focused_text);
                let focused_line = focused_text.char_to_line(focused_head);
                let focused_kind = classify_doc(focused_doc);

                let mut linked_lines: HashSet<usize> = HashSet::new();

                match (focused_kind, doc_kind) {
                    (DocKind::Asm, DocKind::Source) => {
                        if let Some((src_path, target_line_1based)) =
                            nearest_source_loc(focused_text, focused_line)
                        {
                            if path_matches_doc(doc, &src_path) && target_line_1based > 0 {
                                linked_lines.insert(target_line_1based - 1);
                            }
                        }
                    }
                    (DocKind::Source, DocKind::Asm) => {
                        if let Some(focused_path) = focused_doc.path() {
                            linked_lines =
                                collect_matching_asm_lines(text, focused_path, focused_line + 1);
                        }
                    }
                    (DocKind::Asm, DocKind::Mca) => {
                        if let Some(idx) = asm_line_to_mca_index(focused_text, focused_line, text) {
                            linked_lines = find_all_mca_lines_for_index(text, idx);
                        }
                    }
                    (DocKind::Mca, DocKind::Asm) => {
                        if let Some(mca_ref) = parse_mca_line_insn_ref(focused_text, focused_line) {
                            if let Some(asm_line) =
                                resolve_mca_ref_to_asm_line(text, focused_text, &mca_ref)
                            {
                                linked_lines.insert(asm_line);
                            }
                        }
                    }
                    (DocKind::Mca, DocKind::Source) => {
                        if let Some(mca_ref) = parse_mca_line_insn_ref(focused_text, focused_line) {
                            if let Some(asm_doc) = find_open_doc_of_kind(editor, DocKind::Asm) {
                                let asm_text = asm_doc.text().slice(..);
                                if let Some(asm_line) =
                                    resolve_mca_ref_to_asm_line(asm_text, focused_text, &mca_ref)
                                {
                                    if let Some((src_path, l1)) =
                                        nearest_source_loc(asm_text, asm_line)
                                    {
                                        if path_matches_doc(doc, &src_path) && l1 > 0 {
                                            linked_lines.insert(l1 - 1);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    (DocKind::Source, DocKind::Mca) => {
                        if let Some(focused_path) = focused_doc.path() {
                            if let Some(asm_doc) = find_open_doc_of_kind(editor, DocKind::Asm) {
                                let asm_text = asm_doc.text().slice(..);
                                let asm_lines = collect_matching_asm_lines(
                                    asm_text,
                                    focused_path,
                                    focused_line + 1,
                                );
                                for asm_line in asm_lines {
                                    if let Some(idx) =
                                        asm_line_to_mca_index(asm_text, asm_line, text)
                                    {
                                        linked_lines.extend(find_all_mca_lines_for_index(text, idx));
                                    }
                                }
                            }
                        }
                    }
                    _ => {}
                }

                if !linked_lines.is_empty() {
                    let style = linked_highlight_style(theme);
                    decorations.add_decoration(move |renderer: &mut TextRenderer, pos: LinePos| {
                        if linked_lines.contains(&pos.doc_line) {
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

    // 2. Jump-target & label highlighting inside focused asm buffers
    if is_focused && doc_kind == DocKind::Asm {
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
    if doc_kind == DocKind::Asm || is_perf_doc(doc) {
        let view_offset = doc.view_offset(view.id);
        let first_line = text.char_to_line(view_offset.anchor.min(text.len_chars()));
        let end_line = (first_line + inner.height as usize + 8).min(total_lines);

        let mut hot_lines: Vec<(usize, u8)> = Vec::new();
        for line_idx in first_line..end_line {
            if let Some(pct) = parse_perf_percent(text.line(line_idx)) {
                if pct >= 15.0 {
                    hot_lines.push((line_idx, 3));
                } else if pct >= 5.0 {
                    hot_lines.push((line_idx, 2));
                } else if pct >= 1.0 {
                    hot_lines.push((line_idx, 1));
                }
            }
        }
        if !hot_lines.is_empty() {
            let s3 = perf_heat_style(theme, 3);
            let s2 = perf_heat_style(theme, 2);
            let s1 = perf_heat_style(theme, 1);
            decorations.add_decoration(move |renderer: &mut TextRenderer, pos: LinePos| {
                if let Ok(idx) = hot_lines.binary_search_by_key(&pos.doc_line, |&(l, _)| l) {
                    let style = match hot_lines[idx].1 {
                        3 => s3,
                        2 => s2,
                        _ => s1,
                    };
                    renderer.set_style(Rect::new(inner.x, pos.visual_line, inner.width, 1), style);
                }
            });
        }
    }
}

/// Viewport-scoped syntax highlight overlays for `llvm-mca` and `perf annotate --stdio` buffers.
pub fn overlay_highlights(
    doc: &Document,
    view: &View,
    inner_height: u16,
    theme: &Theme,
) -> Option<OverlayHighlights> {
    let text = doc.text().slice(..);
    let total_lines = text.len_lines();
    if total_lines == 0 {
        return None;
    }

    let is_mca = is_mca_doc(doc);
    let is_perf = !is_mca && is_perf_annotate_buffer(doc);
    if !is_mca && !is_perf {
        return None;
    }

    let view_offset = doc.view_offset(view.id);
    let first_line = text.char_to_line(view_offset.anchor.min(text.len_chars()));
    let end_line = (first_line + inner_height as usize + 4).min(total_lines);

    let pal = Palette::from_theme(theme);
    let mut highlights: Vec<(Highlight, Range<usize>)> = Vec::new();

    if is_mca {
        for line_idx in first_line..end_line {
            let line_start = text.line_to_char(line_idx);
            let line_str = text.line(line_idx).to_string();
            highlight_mca_line(&line_str, line_start, &pal, &mut highlights);
        }
    } else {
        for line_idx in first_line..end_line {
            let line_start = text.line_to_char(line_idx);
            let line_str = text.line(line_idx).to_string();
            highlight_perf_line(&line_str, line_start, &pal, &mut highlights);
        }
    }

    if highlights.is_empty() {
        return None;
    }
    // Enforce sorted, strictly non-overlapping ranges (invariant required by OverlayHighlights)
    highlights.sort_by_key(|(_, r)| (r.start, r.end));
    let mut clean: Vec<(Highlight, Range<usize>)> = Vec::with_capacity(highlights.len());
    let mut last_end = 0usize;
    for (hl, r) in highlights {
        if r.start < r.end && r.start >= last_end {
            last_end = r.end;
            clean.push((hl, r));
        }
    }
    if clean.is_empty() {
        None
    } else {
        Some(OverlayHighlights::Heterogenous { highlights: clean })
    }
}

struct Palette {
    heading: Option<Highlight>,
    keyword: Option<Highlight>,
    function: Option<Highlight>,
    register: Option<Highlight>,
    number: Option<Highlight>,
    comment: Option<Highlight>,
    err: Option<Highlight>,
    warn: Option<Highlight>,
    ok: Option<Highlight>,
    member: Option<Highlight>,
}

impl Palette {
    fn from_theme(theme: &Theme) -> Self {
        let pick = |names: &[&str]| names.iter().find_map(|n| theme.find_highlight(n));
        Self {
            heading: pick(&["markup.heading", "type", "keyword"]),
            keyword: pick(&["keyword.control", "keyword", "type.builtin"]),
            function: pick(&["function", "markup.link.url", "string"]),
            register: pick(&["variable.builtin", "variable.parameter", "variable"]),
            number: pick(&["constant.numeric", "constant"]),
            comment: pick(&["comment", "ui.virtual"]),
            err: pick(&["diagnostic.error", "diff.minus", "error", "type"]),
            warn: pick(&["diagnostic.warning", "warning", "diff.delta", "constant.numeric"]),
            ok: pick(&["diff.plus", "string", "constant.numeric"]),
            member: pick(&["variable.other.member", "attribute", "label"]),
        }
    }
}

fn push_byte_span(
    out: &mut Vec<(Highlight, Range<usize>)>,
    hl: Option<Highlight>,
    line: &str,
    line_char_start: usize,
    b0: usize,
    b1: usize,
) {
    let Some(hl) = hl else { return };
    if b0 >= b1 || b1 > line.len() {
        return;
    }
    let c0 = line[..b0].chars().count();
    let c1 = c0 + line[b0..b1].chars().count();
    out.push((hl, (line_char_start + c0)..(line_char_start + c1)));
}

fn highlight_mca_line(
    line: &str,
    line_start: usize,
    pal: &Palette,
    out: &mut Vec<(Highlight, Range<usize>)>,
) {
    let line_no_nl = line.trim_end_matches(['\r', '\n']);
    let trimmed = line_no_nl.trim();
    if trimmed.is_empty() {
        return;
    }

    // Header comments `; llvm-mca ...`
    if trimmed.starts_with(';') {
        push_byte_span(out, pal.comment, line_no_nl, line_start, 0, line_no_nl.len());
        return;
    }
    // Warnings & notes
    if line_no_nl.starts_with("warning:") {
        push_byte_span(out, pal.warn, line_no_nl, line_start, 0, 8);
        push_byte_span(out, pal.comment, line_no_nl, line_start, 8, line_no_nl.len());
        return;
    }
    if line_no_nl.starts_with("note:") {
        push_byte_span(out, pal.comment, line_no_nl, line_start, 0, line_no_nl.len());
        return;
    }
    // Section headers
    if matches!(
        trimmed,
        "Instruction Info:"
            | "Resources:"
            | "Resource pressure per iteration:"
            | "Resource pressure by instruction:"
            | "Throughput Bottlenecks:"
            | "Timeline view:"
            | "Average Wait times (based on the timeline view):"
            | "Critical sequence based on the simulation:"
    ) || trimmed.starts_with("Cycles with backend pressure")
    {
        if let Some(br) = line_no_nl.find('[') {
            push_byte_span(out, pal.heading, line_no_nl, line_start, 0, br);
            highlight_bracket_percent(line_no_nl, line_start, br, pal, out);
        } else {
            push_byte_span(out, pal.heading, line_no_nl, line_start, 0, line_no_nl.len());
        }
        return;
    }

    // Summary key: value lines (Iterations, IPC, Block RThroughput, ...)
    for key in [
        "Iterations:",
        "Instructions:",
        "Total Cycles:",
        "Total uOps:",
        "Dispatch Width:",
        "uOps Per Cycle:",
        "IPC:",
        "Block RThroughput:",
    ] {
        if line_no_nl.starts_with(key) {
            push_byte_span(out, pal.member, line_no_nl, line_start, 0, key.len());
            let val_start = key.len()
                + line_no_nl[key.len()..]
                    .find(|c: char| !c.is_whitespace())
                    .unwrap_or(0);
            if val_start < line_no_nl.len() {
                push_byte_span(out, pal.number, line_no_nl, line_start, val_start, line_no_nl.len());
            }
            return;
        }
    }

    // Bottleneck breakdown lines with `[ xx.xx% ]`
    if let Some(br) = line_no_nl.find('[') {
        if line_no_nl[br..].contains("% ]") || line_no_nl[br..].contains("%]") {
            push_byte_span(out, pal.member, line_no_nl, line_start, 0, br);
            highlight_bracket_percent(line_no_nl, line_start, br, pal, out);
            return;
        }
    }

    // Critical sequence lines (` +----> 1. mov rbp, rsp ## REGISTER dependency: rsp`)
    if trimmed.starts_with("+----")
        || trimmed.starts_with('|')
        || trimmed.starts_with("Instruction")
    {
        if let Some(lc) = line_no_nl.find("< loop carried >") {
            push_byte_span(out, pal.warn, line_no_nl, line_start, lc, lc + "< loop carried >".len());
            return;
        }
        if let Some(arrow_pos) = line_no_nl.find("+----") {
            let arrow_end = (arrow_pos + 6).min(line_no_nl.len());
            push_byte_span(out, pal.err, line_no_nl, line_start, arrow_pos, arrow_end);
        }
        // Highlight `## ... dependency` comment at EOL
        let (before_dep, dep_start) = if let Some(d) = line_no_nl.find("##") {
            (&line_no_nl[..d], Some(d))
        } else {
            (line_no_nl, None)
        };
        // Find `<N>.` instruction number then highlight asm instruction
        if let Some((num_start, num_end)) = find_crit_insn_num(before_dep) {
            push_byte_span(out, pal.number, line_no_nl, line_start, num_start, num_end);
            highlight_asm_instruction_span(before_dep, line_start, num_end, pal, out);
        }
        if let Some(d) = dep_start {
            push_byte_span(out, pal.warn, line_no_nl, line_start, d, line_no_nl.len());
        }
        return;
    }

    // Timeline rows: `[0,0]     DeER . . .   push rbp`
    if trimmed.starts_with('[') && trimmed.contains(']') && !trimmed.starts_with("[1]") {
        if let Some(close) = line_no_nl.find(']') {
            push_byte_span(out, pal.number, line_no_nl, line_start, 0, close + 1);
            let rest = &line_no_nl[close + 1..];
            // Find the instruction after the timeline chars (`D`, `e`, `E`, `R`, `=`, `-`, `.`, spaces)
            let mut insn_off = None;
            let bytes = rest.as_bytes();
            let mut i = 0;
            while i < bytes.len() {
                let b = bytes[i];
                if b == b' ' || b == b'\t' {
                    i += 1;
                    continue;
                }
                // Check if token is purely timeline symbols
                let start = i;
                while i < bytes.len() && bytes[i] != b' ' && bytes[i] != b'\t' {
                    i += 1;
                }
                let tok = &rest[start..i];
                let is_tl = tok
                    .bytes()
                    .all(|c| matches!(c, b'D' | b'e' | b'E' | b'R' | b'=' | b'-' | b'.'));
                if is_tl {
                    let hl = if tok.contains('=') {
                        pal.warn
                    } else if tok.contains('E') || tok.contains('e') {
                        pal.ok
                    } else {
                        pal.comment
                    };
                    push_byte_span(
                        out,
                        hl,
                        line_no_nl,
                        line_start,
                        close + 1 + start,
                        close + 1 + i,
                    );
                } else {
                    insn_off = Some(close + 1 + start);
                    break;
                }
            }
            if let Some(off) = insn_off {
                highlight_asm_instruction_span(line_no_nl, line_start, off, pal, out);
            }
            return;
        }
    }

    // Instruction Info / Resource pressure table header `[1] [2] ...`
    if trimmed.starts_with('[') {
        push_byte_span(out, pal.comment, line_no_nl, line_start, 0, line_no_nl.len());
        return;
    }

    // Instruction Info row: ` 1      8     0.33    *                   vmovups ...`
    if let Some((col_end, lat_span, lat_val)) = parse_mca_insn_info_spans(line_no_nl) {
        let lat_hl = if lat_val >= 8 {
            pal.err
        } else if lat_val >= 4 {
            pal.warn
        } else {
            pal.number
        };
        push_byte_span(out, lat_hl, line_no_nl, line_start, lat_span.start, lat_span.end);
        highlight_asm_instruction_span(line_no_nl, line_start, col_end, pal, out);
    }
}

fn highlight_bracket_percent(
    line: &str,
    line_start: usize,
    br_start: usize,
    pal: &Palette,
    out: &mut Vec<(Highlight, Range<usize>)>,
) {
    let Some(rel_end) = line[br_start..].find(']') else {
        return;
    };
    let end = br_start + rel_end + 1;
    let inner = line[br_start + 1..br_start + rel_end].trim().trim_end_matches('%');
    let pct = inner.parse::<f32>().unwrap_or(0.0);
    let hl = if pct >= 20.0 {
        pal.err
    } else if pct >= 5.0 {
        pal.warn
    } else {
        pal.ok
    };
    push_byte_span(out, hl, line, line_start, br_start, end);
}

fn highlight_perf_line(
    line: &str,
    line_start: usize,
    pal: &Palette,
    out: &mut Vec<(Highlight, Range<usize>)>,
) {
    let line_no_nl = line.trim_end_matches(['\r', '\n']);
    let trimmed = line_no_nl.trim_start();
    if trimmed.is_empty() {
        return;
    }
    if trimmed.starts_with(';') {
        push_byte_span(out, pal.comment, line_no_nl, line_start, 0, line_no_nl.len());
        return;
    }
    let Some(colon_rel) = trimmed.find(':') else {
        return;
    };
    let lead = line_no_nl.len() - trimmed.len();
    let pct_str = trimmed[..colon_rel].trim();
    let Ok(pct) = pct_str.parse::<f32>() else {
        return;
    };
    let pct_hl = if pct >= 15.0 {
        pal.err
    } else if pct >= 5.0 {
        pal.warn
    } else if pct >= 1.0 {
        pal.number
    } else {
        pal.comment
    };
    push_byte_span(out, pct_hl, line_no_nl, line_start, lead, lead + colon_rel);

    let after_colon = lead + colon_rel + 1;
    let rest = &line_no_nl[after_colon..];
    let rest_trim = rest.trim_start();
    let addr_start = after_colon + (rest.len() - rest_trim.len());

    // Optional hex address `109bc08:`
    let insn_start = if let Some(addr_colon) = rest_trim.find(':') {
        let maybe_hex = &rest_trim[..addr_colon];
        if !maybe_hex.is_empty() && maybe_hex.chars().all(|c| c.is_ascii_hexdigit()) {
            let addr_end = addr_start + addr_colon + 1;
            push_byte_span(out, pal.comment, line_no_nl, line_start, addr_start, addr_end);
            addr_end
        } else {
            addr_start
        }
    } else {
        addr_start
    };

    highlight_asm_instruction_span(line_no_nl, line_start, insn_start, pal, out);
}

fn highlight_asm_instruction_span(
    line: &str,
    line_start: usize,
    from_byte: usize,
    pal: &Palette,
    out: &mut Vec<(Highlight, Range<usize>)>,
) {
    if from_byte >= line.len() {
        return;
    }
    let slice = &line[from_byte..];
    let ws = slice.find(|c: char| !c.is_whitespace()).unwrap_or(slice.len());
    let mnem_start = from_byte + ws;
    if mnem_start >= line.len() {
        return;
    }
    let mnem_len = line[mnem_start..]
        .find(|c: char| c.is_whitespace())
        .unwrap_or(line.len() - mnem_start);
    let mnem_end = mnem_start + mnem_len;
    push_byte_span(out, pal.keyword, line, line_start, mnem_start, mnem_end);

    // Scan operands for `<symbol>`, registers, and numeric literals
    let bytes = line.as_bytes();
    let mut i = mnem_end;
    while i < bytes.len() {
        let b = bytes[i];
        if b == b'<' {
            if let Some(close) = line[i..].find('>') {
                push_byte_span(out, pal.function, line, line_start, i, i + close + 1);
                i += close + 1;
                continue;
            }
        }
        if b == b';' || b == b'#' {
            push_byte_span(out, pal.comment, line, line_start, i, bytes.len());
            break;
        }
        if b.is_ascii_alphanumeric() || b == b'%' || b == b'$' || b == b'.' || b == b'_' {
            let start = i;
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric()
                    || matches!(bytes[i], b'%' | b'$' | b'.' | b'_'))
            {
                i += 1;
            }
            let tok = &line[start..i];
            if is_asm_register(tok) {
                push_byte_span(out, pal.register, line, line_start, start, i);
            } else if is_asm_number(tok) {
                push_byte_span(out, pal.number, line, line_start, start, i);
            }
            continue;
        }
        i += 1;
    }
}

fn is_asm_register(tok: &str) -> bool {
    let t = tok.strip_prefix('%').unwrap_or(tok);
    if matches!(
        t,
        "rax" | "rbx" | "rcx" | "rdx" | "rsi" | "rdi" | "rbp" | "rsp" | "rip"
            | "eax" | "ebx" | "ecx" | "edx" | "esi" | "edi" | "ebp" | "esp"
            | "ax" | "bx" | "cx" | "dx" | "si" | "di" | "bp" | "sp"
            | "al" | "bl" | "cl" | "dl" | "sil" | "dil" | "bpl" | "spl"
            | "ah" | "bh" | "ch" | "dh"
            | "xzr" | "wzr" | "lr" | "fp"
    ) {
        return true;
    }
    // r8..r15[d|w|b], xmm0..31, ymm0..31, zmm0..31, k0..7, x0..30, w0..30, v0..31
    if let Some(rest) = t.strip_prefix("xmm").or_else(|| t.strip_prefix("ymm")).or_else(|| t.strip_prefix("zmm")) {
        return !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit());
    }
    if let Some(rest) = t.strip_prefix('r') {
        let digits = rest.trim_end_matches(['d', 'w', 'b']);
        if let Ok(n) = digits.parse::<u8>() {
            return (8..=15).contains(&n);
        }
    }
    if let Some(rest) = t.strip_prefix(['x', 'w', 'v', 'q', 'd', 's']) {
        if let Ok(n) = rest.parse::<u8>() {
            return n <= 31;
        }
    }
    false
}

fn is_asm_number(tok: &str) -> bool {
    let t = tok.strip_prefix('$').unwrap_or(tok);
    if let Some(hex) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        return !hex.is_empty() && hex.bytes().all(|b| b.is_ascii_hexdigit());
    }
    !t.is_empty() && t.bytes().all(|b| b.is_ascii_digit())
}

/// `:mca [mcpu]` — run `llvm-mca` on the visual selection (or enclosing asm function) into a split.
pub fn run_mca(
    cx: &mut compositor::Context,
    args: Args,
    event: PromptEvent,
) -> anyhow::Result<()> {
    if event != PromptEvent::Validate {
        return Ok(());
    }

    let mcpu = args.first().map(|s| s.to_string()).unwrap_or_else(|| "native".to_string());
    let (asm_input, insn_count, is_att, src_label, start_line_1based, end_line_1based) = {
        let (view, doc) = current_ref!(cx.editor);
        let text = doc.text().slice(..);
        if text.len_lines() == 0 {
            cx.editor.set_error("mca: empty buffer");
            return Ok(());
        }
        let sel = doc.selection(view.id).primary();
        let (line_a, line_b) = if sel.len() > 1 {
            let from = text.char_to_line(sel.from());
            let to = text.char_to_line(sel.to().saturating_sub(1).max(sel.from()));
            (from, to)
        } else {
            let cur = text.char_to_line(sel.cursor(text));
            enclosing_asm_function_range(text, cur)
        };

        let (cleaned, count, att) = extract_clean_mca_input(text, line_a, line_b);
        let label = doc
            .relative_path()
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_else(|| "[scratch]".into());
        (cleaned, count, att, label, line_a + 1, line_b + 1)
    };

    if insn_count == 0 {
        cx.editor.set_error("mca: no assembly instructions found in selection");
        return Ok(());
    }

    cx.editor
        .set_status(format!("Running llvm-mca (-mcpu={mcpu}) on {insn_count} insns..."));

    cx.jobs.callback(async move {
        let output = tokio::task::spawn_blocking(move || {
            let mut cmd = Command::new("llvm-mca");
            cmd.arg(format!("-mcpu={mcpu}"))
                .arg("--bottleneck-analysis")
                .arg("--instruction-info")
                .arg("--timeline");
            if !is_att {
                cmd.arg("-x86-asm-syntax=intel");
            }
            cmd.stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped());

            let mut child = cmd.spawn()?;
            if let Some(mut stdin) = child.stdin.take() {
                let _ = stdin.write_all(asm_input.as_bytes());
            }
            let out = child.wait_with_output()?;
            let mut combined = format!(
                "; llvm-mca (mcpu={mcpu}, {insn_count} insns) from {src_label}:{start_line_1based}-{end_line_1based}\n\n"
            );
            if !out.stderr.is_empty() {
                combined.push_str(&String::from_utf8_lossy(&out.stderr));
                if !combined.ends_with('\n') {
                    combined.push('\n');
                }
            }
            combined.push_str(&String::from_utf8_lossy(&out.stdout));
            Ok::<String, std::io::Error>(combined)
        })
        .await;

        let text_out = match output {
            Ok(Ok(s)) => s,
            Ok(Err(e)) => {
                return Ok(Callback::Editor(Box::new(move |editor| {
                    editor.set_error(format!("mca: failed to run llvm-mca: {e}"));
                })));
            }
            Err(e) => {
                return Ok(Callback::Editor(Box::new(move |editor| {
                    editor.set_error(format!("mca: task error: {e}"));
                })));
            }
        };

        Ok(Callback::Editor(Box::new(move |editor| {
            // Reuse an existing scratch MCA split if open, else open a new vertical split
            let existing_mca = editor
                .tree
                .views()
                .find_map(|(v, _)| {
                    let d = editor.document(v.doc)?;
                    (d.path().is_none() && is_mca_doc(d)).then_some((v.id, d.id()))
                });

            let (view_id, doc_id) = if let Some((vid, did)) = existing_mca {
                (vid, did)
            } else {
                let prev_focus = editor.tree.focus;
                let did = editor.new_file(Action::VerticalSplit);
                let vid = editor.tree.focus;
                editor.tree.focus = prev_focus;
                (vid, did)
            };

            if let Some(doc) = editor.document_mut(doc_id) {
                let len = doc.text().len_chars();
                let tx = Transaction::change(
                    doc.text(),
                    [(0, len, Some(Tendril::from(text_out)))].into_iter(),
                );
                doc.apply(&tx, view_id);
                doc.set_selection(view_id, Selection::point(0));
            }
            editor.set_status("llvm-mca complete (linked with asm + source splits)");
        })))
    });

    Ok(())
}

fn enclosing_asm_function_range(text: RopeSlice<'_>, cur_line: usize) -> (usize, usize) {
    let total = text.len_lines();
    if total == 0 {
        return (0, 0);
    }
    let mut start = cur_line.min(total - 1);
    while start > 0 {
        if is_function_label(text.line(start)) {
            break;
        }
        start -= 1;
    }
    // If cursor is on header comments above the first function label, advance start to that function.
    if !is_function_label(text.line(start)) {
        for l in start..total {
            if is_function_label(text.line(l)) {
                start = l;
                break;
            }
        }
    }
    let mut end = start;
    while end + 1 < total {
        end += 1;
        if is_function_label(text.line(end)) {
            end -= 1;
            break;
        }
    }
    (start, end)
}

fn extract_clean_mca_input(
    text: RopeSlice<'_>,
    start_line: usize,
    end_line: usize,
) -> (String, usize, bool) {
    let mut out = String::new();
    let mut count = 0usize;
    let mut att_hints = 0usize;
    let end = end_line.min(text.len_lines().saturating_sub(1));

    for line_idx in start_line..=end {
        if let Some(insn) = clean_single_asm_line_for_mca(&text.line(line_idx).to_string()) {
            if insn.contains('%') {
                att_hints += 1;
            }
            out.push_str(&insn);
            out.push('\n');
            count += 1;
        }
    }
    (out, count, att_hints > 0)
}

fn clean_single_asm_line_for_mca(raw: &str) -> Option<String> {
    let mut s = raw.trim();
    if s.is_empty() || s.starts_with(';') || s.starts_with('#') || s.starts_with("//") {
        return None;
    }
    // Strip optional `perf annotate` leading `53.15 :`
    if let Some(colon) = s.find(':') {
        let prefix = s[..colon].trim();
        if !prefix.is_empty() && prefix.contains('.') && prefix.parse::<f32>().is_ok() {
            s = s[colon + 1..].trim_start();
        }
    }
    // Strip optional objdump hex address `109bc08:`
    if let Some(colon) = s.find(':') {
        let prefix = s[..colon].trim();
        if !prefix.is_empty() && prefix.chars().all(|c| c.is_ascii_hexdigit()) {
            s = s[colon + 1..].trim_start();
        }
    }
    // Strip EOL comments
    if let Some(i) = s.find(';') {
        s = s[..i].trim();
    }
    if let Some(i) = s.find('#') {
        s = s[..i].trim();
    }
    if let Some(i) = s.find("//") {
        s = s[..i].trim();
    }
    if s.is_empty() || s.starts_with('.') || s.ends_with(':') {
        return None;
    }
    // Strip `<...>` symbolization brackets so llvm-mca parses cleanly
    let cleaned = s.replace(['<', '>'], "");
    let cleaned = cleaned.trim();
    if cleaned.is_empty() {
        None
    } else {
        Some(cleaned.to_string())
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

    let cleaned = raw
        .trim()
        .trim_matches(|c: char| matches!(c, ',' | ';' | ')' | '(' | '[' | ']'));
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

// ---------------------------------------------------------------------------
// MCA <-> ASM index & critical-path mapping helpers
// ---------------------------------------------------------------------------

struct McaInsnRef {
    index: usize,
    insn_text: String,
}

fn find_open_doc_of_kind<'a>(editor: &'a Editor, kind: DocKind) -> Option<&'a Document> {
    editor.tree.views().find_map(|(v, _)| {
        let doc = editor.document(v.doc)?;
        (classify_doc(doc) == kind).then_some(doc)
    })
}

/// Parse `; llvm-mca (...) from <file>:<start>-<end>` header if present (0-based line range).
fn parse_mca_origin_range(mca_text: RopeSlice<'_>) -> Option<(usize, usize)> {
    let first = mca_text.line(0).to_string();
    let from_pos = first.find(" from ")?;
    let loc = first[from_pos + 6..].trim();
    let colon = loc.rfind(':')?;
    let range_part = &loc[colon + 1..];
    let (a, b) = range_part.split_once('-')?;
    let l0 = a.parse::<usize>().ok()?.saturating_sub(1);
    let l1 = b.parse::<usize>().ok()?.saturating_sub(1);
    Some((l0, l1))
}

fn collect_asm_instruction_lines(
    asm_text: RopeSlice<'_>,
    mca_text: RopeSlice<'_>,
) -> Vec<(usize, String)> {
    let total = asm_text.len_lines();
    if total == 0 {
        return Vec::new();
    }
    let (start, end) = parse_mca_origin_range(mca_text)
        .map(|(a, b)| (a.min(total - 1), b.min(total - 1)))
        .unwrap_or((0, total.saturating_sub(1).min(20_000)));

    let mut out = Vec::new();
    for line_idx in start..=end {
        if let Some(clean) = clean_single_asm_line_for_mca(&asm_text.line(line_idx).to_string()) {
            out.push((line_idx, clean));
        }
    }
    out
}

fn asm_line_to_mca_index(
    asm_text: RopeSlice<'_>,
    asm_line: usize,
    mca_text: RopeSlice<'_>,
) -> Option<usize> {
    let insns = collect_asm_instruction_lines(asm_text, mca_text);
    insns.iter().position(|(l, _)| *l == asm_line)
}

fn resolve_mca_ref_to_asm_line(
    asm_text: RopeSlice<'_>,
    mca_text: RopeSlice<'_>,
    mca_ref: &McaInsnRef,
) -> Option<usize> {
    let insns = collect_asm_instruction_lines(asm_text, mca_text);
    if let Some(&(line_idx, ref asm_str)) = insns.get(mca_ref.index) {
        if same_mnemonic(asm_str, &mca_ref.insn_text) {
            return Some(line_idx);
        }
    }
    // Fallback: closest instruction matching the mnemonic if objdump vs .s had minor count drift
    let target_mnem = first_word(&mca_ref.insn_text);
    let mut best: Option<(usize, usize)> = None;
    for (i, &(line_idx, ref asm_str)) in insns.iter().enumerate() {
        if first_word(asm_str) == target_mnem {
            let dist = i.abs_diff(mca_ref.index);
            if best.is_none_or(|(_, d)| dist < d) {
                best = Some((line_idx, dist));
            }
        }
    }
    best.map(|(l, _)| l)
}

fn first_word(s: &str) -> &str {
    s.split_whitespace().next().unwrap_or("")
}

fn same_mnemonic(a: &str, b: &str) -> bool {
    first_word(a).eq_ignore_ascii_case(first_word(b))
}

fn parse_mca_line_insn_ref(mca_text: RopeSlice<'_>, line_idx: usize) -> Option<McaInsnRef> {
    let line_str = mca_text.line(line_idx).to_string();
    let trimmed = line_str.trim();

    // 1. Critical sequence: ` +----> 1.    mov rbp, rsp  ## ...`
    if trimmed.starts_with("+----") || trimmed.starts_with('|') {
        let before_dep = line_str.split("##").next().unwrap_or(&line_str);
        if let Some((ns, ne)) = find_crit_insn_num(before_dep) {
            let idx = before_dep[ns..ne - 1].trim().parse::<usize>().ok()?;
            let insn = before_dep[ne..].trim().to_string();
            if !insn.is_empty() {
                return Some(McaInsnRef {
                    index: idx,
                    insn_text: insn,
                });
            }
        }
        return None;
    }

    // 2. Timeline view: `[0,1]     D=eER . .   mov rbp, rsp`
    if trimmed.starts_with('[') && !trimmed.starts_with("[1]") {
        if let Some(close) = trimmed.find(']') {
            let inside = &trimmed[1..close];
            if let Some((_, idx_str)) = inside.split_once(',') {
                if let Ok(idx) = idx_str.trim().parse::<usize>() {
                    let rest = &trimmed[close + 1..];
                    // Skip timeline symbols to find instruction
                    let insn = rest
                        .split_whitespace()
                        .skip_while(|t| {
                            t.bytes().all(|c| {
                                matches!(c, b'D' | b'e' | b'E' | b'R' | b'=' | b'-' | b'.')
                            })
                        })
                        .collect::<Vec<_>>()
                        .join(" ");
                    if !insn.is_empty() {
                        return Some(McaInsnRef {
                            index: idx,
                            insn_text: insn,
                        });
                    }
                }
            }
        }
        return None;
    }

    // 3. Sequential tables (`Instruction Info` or `Resource pressure by instruction`)
    // Walk backward to the nearest table header (`[1] ... Instructions:` or `Resource pressure by instruction:`)
    let mut header_line = None;
    for l in (0..line_idx).rev() {
        let s = mca_text.line(l).to_string();
        let t = s.trim();
        if t.is_empty() {
            break;
        }
        if (t.starts_with("[1]") && t.contains("Instructions:"))
            || (t.starts_with('[') && t.contains("Instructions:"))
        {
            header_line = Some(l);
            break;
        }
    }
    let hline = header_line?;
    let idx = line_idx - hline - 1;
    let insn = extract_table_row_insn(&line_str)?;
    Some(McaInsnRef {
        index: idx,
        insn_text: insn,
    })
}

fn extract_table_row_insn(line: &str) -> Option<String> {
    if let Some((col_end, _, _)) = parse_mca_insn_info_spans(line) {
        let insn = line[col_end..].trim();
        if !insn.is_empty() {
            return Some(insn.to_string());
        }
    }
    // Resource pressure by instruction row: numbers/`-` followed by instruction
    let mut tokens = line.split_whitespace().peekable();
    while let Some(&tok) = tokens.peek() {
        if tok == "-" || tok.parse::<f32>().is_ok() {
            tokens.next();
        } else {
            break;
        }
    }
    let rest: Vec<&str> = tokens.collect();
    if rest.is_empty() {
        None
    } else {
        Some(rest.join(" "))
    }
}

fn find_mca_line_for_index(mca_text: RopeSlice<'_>, insn_idx: usize) -> Option<usize> {
    find_all_mca_lines_for_index(mca_text, insn_idx).into_iter().min()
}

fn find_all_mca_lines_for_index(mca_text: RopeSlice<'_>, insn_idx: usize) -> HashSet<usize> {
    let mut lines = HashSet::new();
    let total = mca_text.len_lines().min(20_000);
    let mut in_seq_table_start: Option<usize> = None;

    for l in 0..total {
        let s = mca_text.line(l).to_string();
        let t = s.trim();

        if t.is_empty() {
            in_seq_table_start = None;
            continue;
        }
        if t.starts_with('[') && t.contains("Instructions:") {
            in_seq_table_start = Some(l + 1);
            continue;
        }
        if let Some(start) = in_seq_table_start {
            if l - start == insn_idx {
                lines.insert(l);
            }
            continue;
        }
        // Critical sequence entry `<idx>.`
        if t.starts_with("+----") || t.starts_with('|') {
            let before_dep = s.split("##").next().unwrap_or(&s);
            if let Some((ns, ne)) = find_crit_insn_num(before_dep) {
                if before_dep[ns..ne - 1].trim().parse::<usize>().ok() == Some(insn_idx) {
                    lines.insert(l);
                }
            }
        }
        // Timeline first iteration `[0,<idx>]`
        if let Some(rest) = t.strip_prefix("[0,") {
            if let Some(close) = rest.find(']') {
                if rest[..close].trim().parse::<usize>().ok() == Some(insn_idx) {
                    lines.insert(l);
                }
            }
        }
    }
    lines
}

fn collect_mca_critical_indices(mca_text: RopeSlice<'_>) -> HashMap<usize, String> {
    let mut out = HashMap::new();
    let total = mca_text.len_lines().min(20_000);
    let mut in_crit = false;
    for l in 0..total {
        let s = mca_text.line(l).to_string();
        let t = s.trim();
        if t.starts_with("Critical sequence based on") {
            in_crit = true;
            continue;
        }
        if !in_crit {
            continue;
        }
        if t.starts_with("Instruction Info:")
            || t.starts_with("Resources:")
            || t.starts_with("Timeline view:")
        {
            break;
        }
        if t.starts_with("+----") || t.starts_with('|') {
            let before_dep = s.split("##").next().unwrap_or(&s);
            if let Some((ns, ne)) = find_crit_insn_num(before_dep) {
                if let Ok(idx) = before_dep[ns..ne - 1].trim().parse::<usize>() {
                    out.insert(idx, before_dep[ne..].trim().to_string());
                }
            }
        }
    }
    out
}

fn map_mca_indices_to_asm_lines(
    asm_text: RopeSlice<'_>,
    mca_text: RopeSlice<'_>,
    crit_indices: &HashMap<usize, String>,
) -> HashSet<usize> {
    let insns = collect_asm_instruction_lines(asm_text, mca_text);
    let mut out = HashSet::new();
    for (&idx, insn_txt) in crit_indices {
        if let Some(&(line_idx, ref asm_str)) = insns.get(idx) {
            if same_mnemonic(asm_str, insn_txt) {
                out.insert(line_idx);
            }
        }
    }
    out
}

fn find_crit_insn_num(s: &str) -> Option<(usize, usize)> {
    // Matches ` 77.` or ` 0.` after the graph prefix (`+---->`, `|`, spaces)
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i].is_ascii_digit() {
            let start = i;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            if i < bytes.len() && bytes[i] == b'.' {
                return Some((start, i + 1));
            }
        }
        i += 1;
    }
    None
}

fn parse_mca_insn_info_spans(line: &str) -> Option<(usize, Range<usize>, u16)> {
    // Row format: ` 1      8     0.33    *                   vmovups ...`
    let bytes = line.as_bytes();
    let mut i = 0;
    let next_tok = |idx: &mut usize| -> Option<Range<usize>> {
        while *idx < bytes.len() && bytes[*idx].is_ascii_whitespace() {
            *idx += 1;
        }
        let s = *idx;
        while *idx < bytes.len() && !bytes[*idx].is_ascii_whitespace() {
            *idx += 1;
        }
        (s < *idx).then_some(s..*idx)
    };
    let t1 = next_tok(&mut i)?;
    let _uops: u16 = line[t1].parse().ok()?;
    let t2 = next_tok(&mut i)?;
    let lat: u16 = line[t2.clone()].parse().ok()?;
    let t3 = next_tok(&mut i)?;
    let _rtp: f32 = line[t3].parse().ok()?;

    // Skip optional `*` (MayLoad/MayStore) and `U` (HasSideEffects) flags before instruction
    loop {
        let save = i;
        let Some(tok) = next_tok(&mut i) else {
            return None;
        };
        if matches!(&line[tok.clone()], "*" | "U") {
            continue;
        }
        return Some((save, t2, lat));
    }
}

// ---------------------------------------------------------------------------
// Theme styles & generic buffer detectors
// ---------------------------------------------------------------------------

fn is_light_theme(theme: &Theme) -> bool {
    match theme.get("ui.background").bg {
        Some(Color::Rgb(r, g, b)) => (r as u16 + g as u16 + b as u16) > 384,
        _ => false,
    }
}

fn linked_highlight_style(theme: &Theme) -> Style {
    let frameline = theme.get("ui.highlight.frameline");
    if frameline.bg.is_some() {
        return frameline;
    }
    let bg = if is_light_theme(theme) {
        Color::Rgb(215, 232, 250)
    } else {
        Color::Rgb(38, 52, 72)
    };
    Style::default().bg(bg)
}

fn critical_path_style(theme: &Theme) -> Style {
    let bg = if is_light_theme(theme) {
        Color::Rgb(252, 234, 218)
    } else {
        Color::Rgb(54, 34, 26)
    };
    Style::default().bg(bg)
}

fn perf_heat_style(theme: &Theme, level: u8) -> Style {
    let light = is_light_theme(theme);
    let bg = match (light, level) {
        (false, 3) => Color::Rgb(92, 24, 24),   // >= 15% crimson
        (false, 2) => Color::Rgb(78, 42, 18),   // >= 5%  orange-brown
        (false, _) => Color::Rgb(54, 48, 22),   // >= 1%  warm olive
        (true, 3) => Color::Rgb(255, 196, 196),
        (true, 2) => Color::Rgb(255, 222, 186),
        (true, _) => Color::Rgb(252, 244, 196),
    };
    let style = Style::default().bg(bg);
    if level >= 2 {
        style.add_modifier(Modifier::BOLD)
    } else {
        style
    }
}

fn is_mca_doc(doc: &Document) -> bool {
    let text = doc.text().slice(..);
    let check = text.len_lines().min(35);
    for l in 0..check {
        let s = text.line(l).to_string();
        let t = s.trim_start();
        if t.starts_with("; llvm-mca")
            || t.starts_with("Dispatch Width:")
            || t.starts_with("Block RThroughput:")
            || t.starts_with("Instruction Info:")
            || t.starts_with("Throughput Bottlenecks:")
            || t.starts_with("Resource pressure per iteration:")
        {
            return true;
        }
    }
    false
}

fn is_perf_annotate_buffer(doc: &Document) -> bool {
    let text = doc.text().slice(..);
    let check = text.len_lines().min(60);
    let mut hits = 0usize;
    for l in 0..check {
        if parse_perf_percent(text.line(l)).is_some() {
            hits += 1;
            if hits >= 2 {
                return true;
            }
        }
    }
    false
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
        || is_perf_annotate_buffer(doc)
}

/// Parse a source-location header from:
/// - `llvm-objdump --source --line-numbers`: `; /path/file.zig:121`
/// - GNU/AT&T asm comments: `# /path/file.c:42:10`
/// - GNU `objdump -dS -l`: `/path/file.c:121` or `src/file.c:121 (discriminator 2)`
fn parse_source_loc_comment(line: RopeSlice<'_>) -> Option<(String, usize)> {
    let s = line.to_string();
    let trimmed = s.trim();
    let rest = if let Some(r) = trimmed.strip_prefix(';').or_else(|| trimmed.strip_prefix('#')) {
        r.trim()
    } else if !s.starts_with(' ') && !s.starts_with('\t') && trimmed.contains('/') {
        trimmed
    } else {
        return None;
    };
    let rest = rest.split(" (discriminator").next()?.trim();
    if rest.is_empty() || rest.contains(' ') {
        return None;
    }
    let mut parts = rest.rsplitn(3, ':');
    let last = parts.next()?;
    let prev = parts.next()?;
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

fn is_branch_mnemonic(mnem: &str) -> bool {
    if mnem.starts_with('j') || matches!(mnem, "loop" | "loope" | "loopne") {
        return true;
    }
    mnem == "b" || mnem.starts_with("b.") || matches!(mnem, "cbz" | "cbnz" | "tbz" | "tbnz")
}

fn extract_branch_target(code: &str) -> Option<&str> {
    let mut parts = code.split_whitespace();
    let mnem = parts.next()?;
    if !is_branch_mnemonic(mnem) {
        return None;
    }
    let rest = code[mnem.len()..].trim();
    let operand = rest.rsplit(',').next()?.trim();
    let tok = operand.split_whitespace().last()?;
    let clean = tok.trim_matches(|c| c == '<' || c == '>');
    is_valid_label_token(clean).then_some(clean)
}

fn extract_cursor_label(line: RopeSlice<'_>) -> Option<String> {
    let s = line.to_string();
    let code = s
        .split(';')
        .next()
        .unwrap_or("")
        .split("//")
        .next()
        .unwrap_or("")
        .trim();
    if code.is_empty() {
        return None;
    }
    if let Some(lbl) = code.strip_suffix(':') {
        let lbl = lbl.trim_matches(|c| c == '<' || c == '>');
        if is_valid_label_token(lbl) {
            return Some(lbl.to_string());
        }
        return None;
    }
    extract_branch_target(code).map(str::to_string)
}

fn line_matches_label(line: RopeSlice<'_>, label: &str) -> bool {
    let s = line.to_string();
    let code = s
        .split(';')
        .next()
        .unwrap_or("")
        .split("//")
        .next()
        .unwrap_or("")
        .trim();
    if let Some(def) = code.strip_suffix(':') {
        return def.trim_matches(|c| c == '<' || c == '>') == label;
    }
    extract_branch_target(code) == Some(label)
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
    let is_num_char = |c: char| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '+' | '-');
    let mut start = pos;
    while start > 0 && is_num_char(text.char(start - 1)) {
        let prev = text.char(start - 1);
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

// ---------------------------------------------------------------------------
// Smart `gf` path[:line[:col]] + `gd` asm label jump
// ---------------------------------------------------------------------------

/// Try to resolve a `path`, `path:line`, `path:line:col`, or `path#Lline` under cursor/selection.
///
/// Single match jumps directly (pushing jumplist); multiple matches open a Picker with preview.
pub fn try_goto_path_at_cursor(cx: &mut commands::Context, action: Action) -> bool {
    let (raw_token, doc_dir, workspace_root) = {
        let (view, doc) = current_ref!(cx.editor);
        let text = doc.text().slice(..);
        let sel = doc.selection(view.id).primary();
        let frag = sel.fragment(text).to_string();
        let token = if frag.trim().len() > 1 {
            frag.trim().to_string()
        } else {
            extract_path_token(text, sel.cursor(text))
        };
        let doc_dir = doc
            .path()
            .and_then(|p| p.parent())
            .map(Path::to_path_buf)
            .unwrap_or_else(helix_stdx::env::current_working_dir);
        let ws_root = doc.workspace_root();
        (token, doc_dir, ws_root)
    };

    let Some((raw_path, line, col)) = parse_path_and_loc(&raw_token) else {
        return false;
    };

    let matches = resolve_path_candidates(&raw_path, &doc_dir, &workspace_root);
    if matches.is_empty() {
        return false;
    }

    if matches.len() == 1 {
        open_and_jump(cx.editor, &matches[0], line, col, action);
        return true;
    }

    let picker_data = (workspace_root.to_path_buf(), line, col);
    let columns = [PickerColumn::new(
        "path",
        |item: &PathBuf, (root, line, col): &(PathBuf, Option<usize>, Option<usize>)| {
            let rel = item.strip_prefix(root).unwrap_or(item).to_string_lossy();
            match (*line, *col) {
                (Some(l), Some(c)) => format!("{rel}:{l}:{c}").into(),
                (Some(l), None) => format!("{rel}:{l}").into(),
                _ => rel.into_owned().into(),
            }
        },
    )];

    let picker = Picker::new(columns, 0, matches, picker_data, move |cx, path, picker_action| {
        let act = if matches!(picker_action, Action::Replace) {
            action
        } else {
            picker_action
        };
        open_and_jump(cx.editor, path, line, col, act);
    })
    .with_preview(move |_editor, path| {
        let range = line.map(|l| {
            let l0 = l.saturating_sub(1);
            (l0, l0)
        });
        Some((PathOrId::Path(path.as_path()), range))
    });
    cx.push_layer(Box::new(overlaid(picker)));
    true
}

/// In `.asm`/`.s` buffers, jump from a branch target (`jne L6`) to its label definition (`L6:`).
pub fn try_goto_asm_label(cx: &mut commands::Context) -> bool {
    let scrolloff = cx.editor.config().scrolloff;
    let (view, doc) = current!(cx.editor);
    if !is_asm_doc(doc) {
        return false;
    }
    let target_pos = {
        let text = doc.text().slice(..);
        let cursor = doc.selection(view.id).primary().cursor(text);
        let cur_line = text.char_to_line(cursor);
        let Some(label) = extract_cursor_label(text.line(cur_line)) else {
            return false;
        };

        let mut target_line = None;
        for line_idx in 0..text.len_lines() {
            if line_idx == cur_line {
                continue;
            }
            let s = text.line(line_idx).to_string();
            let code = s.split(';').next().unwrap_or("").trim();
            if let Some(def) = code.strip_suffix(':') {
                if def.trim_matches(|c| c == '<' || c == '>') == label {
                    target_line = Some(line_idx);
                    break;
                }
            }
        }
        target_line.map(|line_idx| text.line_to_char(line_idx))
    };

    let Some(pos) = target_pos else {
        return false;
    };
    view.push_jump(doc);
    doc.set_selection(view.id, Selection::point(pos));
    view.ensure_cursor_in_view_center(doc, scrolloff);
    true
}

fn open_and_jump(
    editor: &mut Editor,
    path: &Path,
    line_1based: Option<usize>,
    col_1based: Option<usize>,
    action: Action,
) {
    {
        let (view, doc) = current!(editor);
        view.push_jump(doc);
    }
    let doc_id = match editor.open(path, action) {
        Ok(id) => id,
        Err(err) => {
            editor.set_error(format!("Open file failed: {err:?}"));
            return;
        }
    };
    let Some(line_1) = line_1based else {
        return;
    };
    let scrolloff = editor.config().scrolloff;
    let (view, doc) = (view_mut!(editor), doc_mut!(editor, &doc_id));
    let text = doc.text().slice(..);
    let total = text.len_lines();
    if total == 0 {
        return;
    }
    let line_idx = line_1.saturating_sub(1).min(total - 1);
    let line_start = text.line_to_char(line_idx);
    let line_len = text.line(line_idx).len_chars();
    let col_off = col_1based
        .unwrap_or(1)
        .saturating_sub(1)
        .min(line_len.saturating_sub(1));
    doc.set_selection(view.id, Selection::point(line_start + col_off));
    view.ensure_cursor_in_view_center(doc, scrolloff);
}

fn extract_path_token(text: RopeSlice<'_>, cursor: usize) -> String {
    let len = text.len_chars();
    if len == 0 {
        return String::new();
    }
    let pos = cursor.min(len.saturating_sub(1));
    let is_path_char = |c: char| {
        c.is_ascii_alphanumeric()
            || matches!(c, '/' | '\\' | '.' | '_' | '-' | ':' | '~' | '$' | '#' | '+')
    };
    let mut start = pos;
    while start > 0 && is_path_char(text.char(start - 1)) {
        start -= 1;
    }
    let mut end = pos;
    while end < len && is_path_char(text.char(end)) {
        end += 1;
    }
    text.slice(start..end).to_string()
}

fn parse_path_and_loc(raw: &str) -> Option<(String, Option<usize>, Option<usize>)> {
    let s = raw.trim().trim_matches(|c: char| {
        matches!(
            c,
            '"' | '\'' | '`' | '(' | ')' | '[' | ']' | '<' | '>' | ',' | ';'
        )
    });
    let s = s.strip_prefix("file://").unwrap_or(s);
    if s.is_empty() || s.starts_with("http://") || s.starts_with("https://") {
        return None;
    }

    if let Some((path, frag)) = s.split_once("#L") {
        let digits: String = frag.chars().take_while(|c| c.is_ascii_digit()).collect();
        let line = digits.parse::<usize>().ok().filter(|&l| l > 0);
        if !path.is_empty() {
            return Some((path.to_string(), line, None));
        }
    }

    let s = s.trim_end_matches(':');
    let mut parts = s.rsplitn(3, ':');
    let last = parts.next()?;
    if let Some(prev) = parts.next() {
        if let Ok(n_last) = last.parse::<usize>() {
            if let Ok(n_prev) = prev.parse::<usize>() {
                if let Some(path) = parts.next() {
                    if !path.is_empty() && n_prev > 0 {
                        return Some((path.to_string(), Some(n_prev), Some(n_last.max(1))));
                    }
                }
            } else if !prev.is_empty() && n_last > 0 {
                let path = &s[..s.len() - last.len() - 1];
                return Some((path.to_string(), Some(n_last), None));
            }
        }
    }

    if s.contains('.') || s.contains('/') {
        return Some((s.to_string(), None, None));
    }
    None
}

fn resolve_path_candidates(raw_path: &str, doc_dir: &Path, workspace_root: &Path) -> Vec<PathBuf> {
    let expanded = helix_stdx::path::expand(Path::new(raw_path));
    let p = expanded.as_ref();

    let direct_candidates = [
        p.to_path_buf(),
        doc_dir.join(p),
        workspace_root.join(p),
        helix_stdx::env::current_working_dir().join(p),
    ];
    for cand in direct_candidates {
        if cand.is_file() {
            return vec![cand];
        }
    }

    let mut results = Vec::new();
    let mut seen = HashSet::new();
    let walker = ignore::WalkBuilder::new(workspace_root)
        .hidden(false)
        .git_ignore(true)
        .max_depth(Some(12))
        .build();

    for entry in walker.flatten() {
        if !entry.file_type().is_some_and(|ft| ft.is_file()) {
            continue;
        }
        let path = entry.path();
        if path.ends_with(p) && seen.insert(path.to_path_buf()) {
            results.push(path.to_path_buf());
            if results.len() >= 50 {
                break;
            }
        }
    }
    results.sort();
    results
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
        let r4 = Rope::from("/projects/Zig/axiom/src/foo.zig:99 (discriminator 2)\n");
        assert_eq!(
            parse_source_loc_comment(r4.line(0)),
            Some(("/projects/Zig/axiom/src/foo.zig".into(), 99))
        );
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
        assert!(line_matches_label(
            Rope::from("    je .LBB280_1\n").line(0),
            ".LBB280_1"
        ));
        assert_eq!(
            extract_cursor_label(Rope::from("    cbnz x0, .LBB0_4 // loop\n").line(0)),
            Some(".LBB0_4".into())
        );
        assert!(line_matches_label(
            Rope::from("    b.eq .LBB0_4\n").line(0),
            ".LBB0_4"
        ));
    }

    #[test]
    fn parses_numbers() {
        assert!(format_number_rows("0x3f80_0000").is_some());
        assert!(format_number_rows("0b1011_0100").is_some());
        assert!(format_number_rows("1e-7").is_some());
        assert!(format_number_rows("-42").is_some());
    }

    #[test]
    fn parses_path_and_line_col() {
        assert_eq!(
            parse_path_and_loc("src/manifold/brep/brep_reader.zig:279"),
            Some(("src/manifold/brep/brep_reader.zig".into(), Some(279), None))
        );
        assert_eq!(
            parse_path_and_loc("src/foo.zig:12:5:"),
            Some(("src/foo.zig".into(), Some(12), Some(5)))
        );
        assert_eq!(
            parse_path_and_loc("file:///projects/Zig/axiom/PLAN.md#L42-L50"),
            Some(("/projects/Zig/axiom/PLAN.md".into(), Some(42), None))
        );
        assert_eq!(
            parse_path_and_loc("brep_reader.zig:279"),
            Some(("brep_reader.zig".into(), Some(279), None))
        );
    }

    #[test]
    fn parses_mca_tables_and_crit_seq() {
        let mca = Rope::from(
            "; llvm-mca (mcpu=native, 2 insns) from intel.asm:10-12\n\
             \n\
             Critical sequence based on the simulation:\n\
             +----> 1.    mov rbp, rsp ## REGISTER dependency: rsp\n\
             \n\
             Instruction Info:\n\
             [1]    [2]    [3]    [4]    [5]    [6]    Instructions:\n\
              2      1     0.50           *            push\trbp\n\
              0      1     0.00                        mov\trbp, rsp\n",
        );
        assert_eq!(parse_mca_origin_range(mca.slice(..)), Some((9, 11)));
        let crit = collect_mca_critical_indices(mca.slice(..));
        assert_eq!(crit.get(&1).map(String::as_str), Some("mov rbp, rsp"));
        let r = parse_mca_line_insn_ref(mca.slice(..), 8).unwrap();
        assert_eq!(r.index, 1);
        assert!(r.insn_text.starts_with("mov"));
    }

    #[test]
    fn enclosing_fn_handles_header_comments() {
        let asm = Rope::from(
            "; LLVM-emitted Intel asm\n\
             ; legend: !!\n\
             \n\
             foo.bar:\n\
             \tpush rbp ; !! 2uop\n\
             \tret ; !! 2uop\n",
        );
        let (a, b) = enclosing_asm_function_range(asm.slice(..), 0);
        let (_, count, att) = extract_clean_mca_input(asm.slice(..), a, b);
        assert_eq!(count, 2);
        assert!(!att);
    }
}
