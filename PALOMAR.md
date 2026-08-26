# Palomar Registry entry

This file is the human-readable alignment note for the Palomar submission surface in this
repository. It is intentionally narrower than the full SpinorLean development.

## Selected result

The compared declaration is:

```lean
Palomar.splitLevi_mem_spin_isometry_range_iff_det_square
```

Under a field `K` with `Invertible (2 : K)`, a finite-dimensional module `V`, a finite-dimensional
submodule `W : Submodule K V`, a finite basis `b` of `W`, a selected basis vector `i`, and an
automorphism `g : W ≃ₗ[K] W`, it states

```lean
QuadraticForm.dualProdIsometry (R := K) g ∈
    Set.range (Palomar.spinIsometryEquiv (Q := QuadraticForm.dualProd K W)) ↔
  ∃ u : Kˣ, LinearEquiv.det g = u ^ 2
```

In words: the hyperbolic isometry induced by a Levi coordinate change is represented by an
ambient spin element exactly when the determinant of that coordinate change is a square unit.
The basis and selected line are explicit parameters because the constructive lift in the proof
uses them; they do not change the mathematical condition being characterized.

## Challenge/Solution boundary

`Challenge.lean` imports only Mathlib. It contains the ambient Clifford-conjugation construction
needed to state the result, with precise docstrings for the definitions that occur in the compared
type. It intentionally leaves the selected theorem as the allowed Challenge hole.

`Solution.lean` repeats those statement-level declarations exactly and imports the substantive
SpinorLean development. Its proof identifies the duplicated ambient action with
`Spinor.spinIsometryEquiv` and invokes
`Spinor.dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_iff_exists_det_eq_sq`, converting
between the existing special-orthogonal homomorphism range and the advertised ambient-isometry
range. Thus the selected statement is not manufactured by a new definition in the Challenge.

The repository's ordinary `Spinor/` sources contain no proof-hole tokens. The deliberate `sorry`
in the Challenge is excluded from the substantive-development count and is the input that
Comparator is expected to replace with the Solution proof. `comparator.json` selects only this
theorem and the statement-facing `Palomar.spinIsometryEquiv` definition. The latter is listed as
a definition target because its type is part of the advertised range and its proof-bearing value
is sensitive to harmless environment-specific elaboration of the duplicated helper proofs; the
Challenge and Solution still contain the same explicit construction, while Comparator checks the
definition's type and the selected theorem's proof. Only `propext`, `Quot.sound`, and
`Classical.choice` are permitted.

## Provenance and scope

The selected result is source-based: it formalizes the split-Levi square-determinant criterion in
the companion preprint [arXiv:2604.26155](https://arxiv.org/abs/2604.26155), while adapting its
special-orthogonal presentation to the current repository's ambient spin-isometry API. The public
paper record describes a rank-at-least-three version; the current Lean theorem is stated with the
actual finite-basis hypotheses exposed by the repository. This metadata does not claim novelty,
priority, human peer review, Palomar acceptance, or a full classification of all orthogonal-group
spin images.

The full project also contains the chosen exterior model, chiral and half-spin APIs, kernel and
projective descent results, split-line square-scaling results, square-class quotient results,
Clifford product norms, and selected low-dimensional classifications. Those results are described
in `README.md`; this Palomar entry records only the selected split-Levi theorem.

The root `LICENSE` is Apache-2.0 for the repository snapshot. Publication assets under `paper/`
retain the separate notices recorded in `paper/THIRD_PARTY_NOTICES.md`.

## Reproducibility and submission checklist

From the exact commit intended for registration:

```bash
bash scripts/verify-palomar.sh
PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh  # macOS local replay only
git status --short
git rev-parse HEAD
```

The second command uses the real pinned Landrun sandbox on Linux; the environment variable is a
deliberate macOS-only local fallback because macOS does not provide Landlock. GitHub Actions runs
the same pinned Comparator/NanoDa workflow with real Landrun.

For the public repository `Arthur742Ramos/SpinorLean`, submit the full 40-character SHA printed by
`git rev-parse HEAD`, select the repository-relative configuration `comparator.json`, and use the
root `formalization.yaml`. A branch name or tag is not a substitute for the commit SHA. The final
registration request must be made explicitly at [submit.palomar-registry.org](https://submit.palomar-registry.org/);
this repository preparation does not authenticate, upload, or register the entry.
