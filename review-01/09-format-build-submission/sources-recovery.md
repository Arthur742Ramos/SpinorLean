# Human audit summary

- Document: source recovery checklist
- Current state: OPEN.
- Did the bots find blockers? yes. A current AACA/EM resubmission package cannot be certified from the present `paper/` directory alone.
- Reviewed manuscript target: `paper/main.tex` and `paper/refs.bib`.
- Old EM PDF usage: historical failure evidence only.

## Needed before resubmission handoff

Recover or assemble the exact source package that will be uploaded for the next AACA submission. The package should be treated as the source of truth for the next platform-built PDF.

## Acceptance criteria

1. The package has one intended manuscript body, not both editable source and a second manuscript PDF concatenated into the reviewer-facing stream.
2. All editable source files required by the platform are present.
3. Bibliography wiring is explicit: either `.bib` with the required style files and sufficient platform build passes, or a generated `.bbl` wired into the TeX source if that is the selected EM-safe route.
4. The AACA class/style route is decided and documented: current stage may allow non-`birkjour`, but accepted/final LaTeX requires `birkjour.cls` and `\documentclass{birkjour}` unless the journal approves otherwise.
5. A current platform-built PDF is produced from that exact package and checked for `[?]`, `??`, undefined citations/references, missing files, and duplicate manuscript bodies.
6. The current EM/ProduXion build log or compiler banner is saved if available.

## Requested evidence

- The exact TeX source package uploaded or to be uploaded.
- Any generated `.bbl`, `.blg`, `.aux`, `.log`, or platform build/error log available from EM.
- A fresh platform-built PDF for the current `paper/` source package.
- EM item-type assignments showing which uploaded files are `Manuscript`, `Figure`, `Supplemental`, or reference-only.
