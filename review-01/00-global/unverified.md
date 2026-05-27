# Human audit summary

- Document: unverified-by-constraint ledger
- Current state: OPEN.
- Did the bots find blockers? yes. Several checks remain intentionally unverified because the user constrained this review to paper-only and no Lean builds.
- Reviewed manuscript target: `paper/main.tex` and `paper/refs.bib`.

## UNVERIFIED-BY-CONSTRAINT

The following items were not checked and must not be inferred from this review:

1. Lean compilation status.
2. Absence of `sorry`, `admit`, or other proof placeholders in Lean files.
3. Correctness or existence of named Lean declarations referenced by the paper.
4. Artifact line counts, file counts, or theorem-index consistency.
5. The current source's local LaTeX compilability.
6. The current source's platform-built PDF output.
7. The current source's EM/ProduXion compiler version.
8. Mathematical correctness of theorems and proofs.

## Why these are unverified

The user explicitly requested a paper-only review and instructed that no Lean-related files be touched and no Lean builds be run. This review also avoided local LaTeX compilation so it would not create local build artifacts or mask the absence of a current platform-built PDF.
