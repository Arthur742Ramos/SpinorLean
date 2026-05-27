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
square-class triviality, Lipschitz factorization-existence wrapper when `2` is invertible,
factorization-level identity/product wrappers proving multiplication of the stored norm units
and square classes, noncanonical chosen Lipschitz square-class wrapper, proved equality of the
norm unit and square class across any two Lipschitz vector factorizations of the same element,
the resulting global Lipschitz-group hom, and noncanonical chosen-lift wrapper on the
Lipschitz linear image, including separated repeated subproducts after permutation into the
repeated shape. The Lipschitz norm modules now isolate the remaining kernel-triviality
condition whose combination with the global Lipschitz-group hom implies lift independence and
then the image-level descent obligations needed to turn the image-level square class into a
monoid homomorphism; they also prove the scalar-unit norm calculation and package the
`LipschitzLinearKernelScalarUnits` bridge, which turns a concrete scalar-kernel theorem into
kernel-triviality, descent, and an image-level hom. The direct conditional image-level hom
wrappers package that final composition without proving scalarity/kernel-triviality globally,
and their range-restriction pullback theorems prove that the image-level hom composes back to
the global Lipschitz-group hom; the companion uniqueness theorems say this pullback
characterizes the image-level hom. The theorem-facing
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
Clifford/Lipschitz substrate, factorization-level Lipschitz product wrappers, and noncanonical
Lipschitz linear-image wrapper / proved global Lipschitz-group hom, remaining
kernel-triviality-to-lift-independence, scalar-kernel bridge, descent-obligation APIs, and
direct conditional image-level hom wrappers with their range-restriction pullback and
uniqueness theorems are
separate projects, not dependencies in the claimed theorem package.
The current artifact proves factorization independence for Lipschitz vector factorizations;
global scalarity/kernel-triviality and full orthogonal-group descent remain explicit conditions.

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
