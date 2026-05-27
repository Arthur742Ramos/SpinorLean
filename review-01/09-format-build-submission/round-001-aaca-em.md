# Human audit summary

- Document: AACA / Editorial Manager format-build review report
- Current state: OPEN.
- Did the bots find blockers? yes. The current `paper/` source is not ready for AACA/EM resubmission without source-package and venue-format fixes.
- Reviewed manuscript target: `paper/main.tex` and `paper/refs.bib` at commit `3013eb1f9dcfb2be61e4d1e2d4238813ed18dacd`.
- Not reviewed as manuscript: `built_editorial_manager_pdf.pdf`; it is historical bad-formatting evidence only.
- Scientific-reviewer basis: the actual sibling CLI run in `review-01/scientific-reviewer-review/` returned `NOT_READY`.

## Scope

This report reviews AACA / Editorial Manager formatting, source-package, and rendered-output readiness for the current repository paper source. It does not review Lean artifacts, Lean proof status, or mathematical correctness.

The sibling `scientific-reviewer review manuscript` command was run on
`paper/main.tex` with `review-01/00-global/aaca-venue-profile.yaml`. It produced
1,562 units and 27,393 missing required checks, including missing
`aaca_birkjour_editorial_manager_audit` evidence. The CLI output is therefore
the fail-closed review baseline; the findings below are the first human-readable
AACA/EM triage extracted from that baseline and the current source.

## Findings

### BLOCKER AACA-EM-001: Current `paper/` package is not a complete AACA/EM submission package

Evidence:

- Scientific-reviewer returned `NOT_READY` and blocked on no declared current final upload-format artifact.
- `paper/` contains only `README.md`, `main.tex`, and `refs.bib`.
- AACA requires all relevant editable source files at every submission/revision; incomplete editable source files can prevent review.
- Current source uses `\bibliography{refs}` at `paper/main.tex:1538`, but no generated `.bbl`, `.bst`, AACA `.cls`, or AACA style/template files are present in `paper/`.

Impact:

The visible repository package is a manuscript source directory, not a verified AACA/EM upload package. A fresh resubmission package must be assembled and audited before upload.

### BLOCKER AACA-EM-002: Current abstract is over AACA's stated word range

Evidence:

- AACA asks for a 150-250 word abstract.
- Deterministic TeX-stripped count of `paper/main.tex` between `\begin{abstract}` and `\end{abstract}` is 460 words.
- Abstract source spans `paper/main.tex:70-120`.

Impact:

If the current source is submitted as the AACA manuscript, the abstract length is outside the AACA range.

### BLOCKER AACA-EM-003: Current source lacks required declaration/data-availability section headings

Evidence:

- AACA asks for `Statements and Declarations` and states incomplete submissions may be returned.
- AACA requires a Data Availability Statement for original research.
- Case-insensitive search of `paper/main.tex` for declaration variants did not find declaration, data availability, competing-interest, funding, code-availability, ethics, consent, author-contribution, or acknowledgments section headings. Hits for `declarations` were unrelated prose about Lean declarations, not submission declarations.
- The current source goes from conclusion to bibliography at `paper/main.tex:1500-1540`.

Impact:

The current source needs an AACA-appropriate declarations/data-availability block before references, or an explicit reason each item is not applicable.

### CONDITIONAL AACA-EM-004: Current source is not in AACA `birkjour` form

Evidence:

- `paper/main.tex:1` is `\documentclass[11pt,a4paper]{article}`.
- AACA provides `birkjour.cls` and says the first line should be `\documentclass{birkjour}` for final LaTeX papers after acceptance.

Impact:

This is stage-conditional. It is not by itself a mathematical/content defect and may not block an initial LaTeX submission. It becomes mandatory for the accepted/final AACA LaTeX version and should be planned before resubmission if the journal expects the Birkhauser template earlier.

### CONDITIONAL AACA-EM-005: Current source uses `alpha` bibliography style instead of AACA numbered reference style

Evidence:

- `paper/main.tex:1537` uses `\bibliographystyle{alpha}`.
- AACA says text citations should be identified by numbers in square brackets and reference-list entries numbered consecutively.
- Citation command inventory in current source found nine `\cite...{...}` commands.

Impact:

If the current source is submitted as-is, the source configuration is not aligned with AACA's numbered citation style. This should be corrected in the AACA resubmission package, but the exact fix depends on the selected AACA/EM bibliography route.

### HISTORICAL PITFALL AACA-EM-006: Prior EM-built PDF duplicated manuscript bodies

Evidence:

- Historical EM PDF hash: `42010e8d18ba656a908d524acf6e6b69fc2eee742d931ee701a25f7a941333be`.
- Extracted text contains `Manuscript` and `access/download;Manuscript;main.tex` near the beginning.
- Extracted text later contains `Reference PDF`, followed by another manuscript body.

Impact:

This is not a current-paper defect because the old EM PDF is not the review target. It is a concrete failure mode to avoid: do not let both editable source and a prebuilt reference PDF concatenate into the reviewer-facing manuscript stream.

### HISTORICAL PITFALL AACA-EM-007: Prior EM-built PDF had unresolved citation and cross-reference markers

Evidence:

- Historical EM PDF extracted text contains 9 occurrences of `[?]` and 53 occurrences of `??`.
- Example citation marker: `Lawson-Michelsohn [?]`.
- Example cross-reference marker: `Theorem ??`.

Impact:

This is not evidence about the current `paper/` source output because no current platform-built PDF was produced in this review. It is a required check for the next platform-built PDF: no `[?]`, `??`, undefined citations/references, missing files, or duplicate manuscript bodies should remain.

### OPEN QUESTION AACA-EM-008: Current platform build log and compiler version are unavailable

Evidence:

- No current EM build log was available.
- The historical EM PDF text extraction did not expose a TeX Live banner.
- Springer generic guidance and Aries generic EM/PM guidance conflict on EM TeX Live versions.

Impact:

Do not assert an actual AACA compiler version from this review. Save the current EM build log if available; otherwise avoid version-sensitive package dependencies or document them explicitly.

## Non-findings

- This report does not claim the current paper has `[?]` or `??` markers; no current platform-built PDF was generated.
- This report does not claim Lean artifacts are wrong; Lean was not inspected by build.
- This report does not claim the old EM PDF is the manuscript under review.
