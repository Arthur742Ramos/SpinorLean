# SpinorLean — Accompanying Paper

This directory holds the LaTeX sources of the academic paper accompanying the
SpinorLean formalization (the first formalization of spinor representations
from Clifford algebras in Lean 4 / Mathlib).

## Files

- `main.tex` — the paper source (article class, self-contained skeleton with
  real prose grounded in the repository).
- `refs.bib` — bibliography (BibTeX, `alpha` style).
- `../THEOREM_INDEX.md` — reader-facing map from paper theorem labels to Lean declarations.

## Building

Any standard LaTeX toolchain should work, e.g.:

```bash
pdflatex main
bibtex   main
pdflatex main
pdflatex main
```

or with `latexmk`:

```bash
latexmk -pdf main.tex
```

## Target Venues

Per `ROADMAP.md` §5.3, the intended submission targets are:

1. **CPP 2027** — Certified Programs and Proofs (deadline ≈ Sep 2026).
2. **ITP 2027** — Interactive Theorem Proving.
3. **Advances in Applied Clifford Algebras** — journal, no fixed deadline,
   a natural fit for the algebraic content.
4. *Journal of Automated Reasoning* (tertiary).

## Status

This is now a **substantive working draft** for ROADMAP §5.1. The paper
contains grounded introduction, related-work, architecture, results,
proof-highlight, lessons-learned, future-work prose, and a companion theorem
index tied to the current Lean files and theorem names.

It is still not submission-ready: evaluation, final exposition polishing,
and the last open mathematical stories (notably the full covering-map
theorem and the complete real Bott-periodicity narrative) remain to be
finished.
