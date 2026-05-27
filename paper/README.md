# SpinorLean — Accompanying Paper

This directory holds the LaTeX sources of the academic paper accompanying the
SpinorLean formalization (the first formalization of spinor representations
from Clifford algebras in Lean 4 / Mathlib).

## Files

- `main.tex` — the submission-ready article source grounded in the repository.
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

## Candidate Venues

Per `ROADMAP.md` §5.3, the intended submission targets are:

1. **CPP 2027** — Certified Programs and Proofs (deadline ≈ Sep 2026).
2. **ITP 2027** — Interactive Theorem Proving.
3. **Advances in Applied Clifford Algebras** — journal, no fixed deadline,
   a natural fit for the algebraic content.
4. *Journal of Automated Reasoning* (tertiary).

## Status

This is a **submission-ready manuscript and artifact package for the exact
finite-basis split-Levi theorem package**. The paper contains the introduction,
related-work context, architecture, results, proof highlights, precise formal
result boundary, keywords/MSC metadata, reproducibility instructions, and
companion theorem index tied to the current Lean files and theorem names.

The formal result boundary is explicit: the submitted theorem package covers the
chosen-model spinor construction, split-rank kernel/non-descent,
Levi-projective action, square-determinant Levi lifts, the determinant-square
necessity theorem, the exact finite-basis split-Levi spin-image iff criterion,
the onto determinant square-class characters with their kernel theorems in
linear coordinates and on the canonical split Levi, the resulting quotient
isomorphisms modulo the corresponding spin-image subgroups to the square-class
group, local split-Levi spinor-norm-facing wrappers for these same characters,
the exact split-line image / double-cover criterion, and the Clifford/Lipschitz
vector-product norm formula with its invertible-vector square-class package, product-order
invariance, repeated-pair square-class cancellation, duplicated-product/subproduct
square-class triviality, and Lipschitz factorization-existence wrapper when `2` is invertible,
including separated repeated subproducts after permutation into the repeated shape. The theorem-facing
real-classification surface now also includes
`RealClassification.PeriodEightTable` and `RealClassification.periodEightTable`,
which collect the split families and first-period definite rows, including the explicit
`Cl(0,5) ≃ Mat₄(ℂ)`, `Cl⁺(0,6) ≃ Mat₄(ℂ)`, `Cl(0,6) ≃ Mat₈(ℝ)`,
`Cl⁺(6,0) ≃ Mat₄(ℂ)`, `Cl(6,0) ≃ Mat₄(ℍ)`,
`Cl⁺(0,7) ≃ Mat₈(ℝ)`, `Cl(0,7) ≃ Mat₈(ℝ) × Mat₈(ℝ)`,
`Cl⁺(0,8) ≃ Mat₈(ℝ) × Mat₈(ℝ)`, `Cl(0,8) ≃ Mat₁₆(ℝ)`,
`Cl(7,0) ≃ Mat₈(ℂ)`, `Cl⁺(7,0) ≃ Mat₈(ℝ)`,
`Cl⁺(8,0) ≃ Mat₈(ℝ) × Mat₈(ℝ)`, and `Cl(8,0) ≃ Mat₁₆(ℝ)` rows.
A recursive arbitrary-signature Bott-periodicity theorem, a full all-orthogonal-group image classification,
and a global orthogonal-group spinor-norm API beyond this factorization-existence
Clifford/Lipschitz substrate are separate projects, not dependencies in the claimed theorem package.

## Final preflight

Use these commands before submission or artifact upload:

```bash
lake exe cache get
bash scripts/verify.sh
cd paper && latexmk -pdf main.tex
```

On Windows PowerShell:

```powershell
lake exe cache get
.\scripts\verify.ps1
Set-Location paper
latexmk -pdf main.tex
```

The verification scripts run `lake build` before checking for forbidden
proof-hole tokens, so the preflight does not list a separate build step.
