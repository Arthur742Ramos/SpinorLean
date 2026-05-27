# Human audit summary

- Document: AACA / Editorial Manager remediation report
- Current state: OPEN.
- Did the bots find blockers? yes. Source-level AACA formatting blockers were addressed, but no-build constraints leave final PDF/log readiness unverified.
- Reviewed manuscript target: `paper/main.tex` and `paper/refs.bib` after paper-side fixes.
- Scientific-reviewer basis: `review` and `improve` were both run after fixes; both remain `NOT_READY` because no upload-format artifact or structured evidence ledger is available.
- Forbidden actions honored: no Lean edits, no Lean/lake commands, no local LaTeX compilation, no push.

## Fixed since round 001

### ADDRESSED AACA-EM-002: Abstract length

The current abstract is 177 words by the same deterministic TeX-stripped count
used in round 001. This is within AACA's 150--250 word range.

### ADDRESSED AACA-EM-003: Statements and declarations

The current source now contains `Statements and Declarations` before the
bibliography, with `Funding`, `Competing interests`, `Data availability`,
`Code availability`, and `Author contributions` paragraphs.

### ADDRESSED AACA-EM-004: AACA class route

The first line is now `\documentclass{birkjour}`. The source package includes
`paper/birkjour.cls`. This is source-level alignment only; it is not yet proved
by a LaTeX or platform build.

### ADDRESSED AACA-EM-005: AACA bibliography style route

The bibliography style is now `spmpsci`, and `paper/spmpsci.bst` is present.
The source still uses `paper/refs.bib`, which is acceptable as source wiring
but must be tested by the platform or a local LaTeX/BibTeX run before upload.
Bibliography entries with DOI metadata now also include explicit
`https://doi.org/...` URL fields where available, matching AACA's DOI-link
guidance.

### ADDRESSED AACA-EM-001: Visible AACA source-package support files

The visible `paper/` package now contains:

- `main.tex`
- `refs.bib`
- `birkjour.cls`
- `spmpsci.bst`
- `cite.sty`
- `THIRD_PARTY_NOTICES.md`
- `README.md`

This resolves the previous visible-package gap for the AACA class/style files.
The package remains build-unverified.

## Remaining blockers under the no-build constraint

### BLOCKER AACA-EM-009: No current platform-built PDF or build log

No current platform-built PDF or EM build log exists for the fixed `paper/`
source package. Therefore the review still cannot prove that the fixed package
renders without `[?]`, `??`, missing-file errors, overfull/underfull box
problems, or platform compiler issues.

### BLOCKER AACA-EM-010: scientific-reviewer final readiness remains fail-closed

After the fixes, `scientific-reviewer review manuscript` still returned
`NOT_READY` with manuscript hash
`9bc7413d26549e60ebd05b12336a42c139e45781daabfb4652256b3723415eb8`,
1,573 units, 27,706 required checks, zero completed checks, and 27,706 missing
checks. The top blocker remains absence of a declared upload-format final
submission artifact. This is expected while builds are forbidden and no
structured check-results ledger has been supplied.

### BLOCKER AACA-EM-011: scientific-reviewer improve remains fail-closed

`scientific-reviewer improve manuscript` was also run after the paper fixes.
It produced the same `NOT_READY` state because no structured check-results
ledger was supplied and no upload-format final artifact exists.

## Next required non-Lean evidence

1. Produce a current AACA/EM platform-built PDF from the fixed `paper/` package.
2. Save the EM/ProduXion build log or compiler banner if available.
3. Verify the current platform-built PDF has no `[?]`, `??`, missing-file
   errors, duplicate manuscript bodies, or declaration/bibliography omissions.
4. If local LaTeX validation is permitted later, run it in a scratch directory
   or clean build folder and record logs without touching Lean.
