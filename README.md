# SpinorLean

First-ever formalization of spinor representations from Clifford algebras in Lean 4 / Mathlib.

## What This Is

The **spinor representation** is one of the most important constructions in mathematics and physics — it's how the Spin group acts on "square roots of geometry." Despite Clifford algebras and Spin groups already existing in Mathlib, nobody has formalized the actual spinor module that connects them.

This project fills that gap.

## Structure

```
SpinorLean/
├── .github/workflows/lean.yml -- CI: Lean build + no-hole check
├── THEOREM_INDEX.md   -- Paper theorem labels mapped to Lean declarations
├── Spinor.lean
├── Spinor/
│   ├── Mathlib.lean        -- Shared Mathlib imports
│   ├── Notation.lean       -- Project conventions and abbreviations
│   ├── Inventory.lean      -- Mathlib audit and documented gaps
│   ├── Isotropic.lean      -- Totally isotropic subspaces
│   ├── WittDecomp.lean     -- Witt index and maximal isotropic existence
│   ├── Basic.lean          -- Exterior-model spinor module alias
│   ├── ExteriorModel.lean  -- Chosen `⋀W` models, dimensions, wedge/contraction operators
│   ├── HyperbolicAction.lean -- Transport of the chosen model along explicit split isometries
│   ├── Presentation.lean   -- First-class explicit hyperbolic presentations and their chosen models
│   ├── ProdNeg.lean        -- Canonical split presentation and chosen model for `Q ⊕ (-Q)`
│   ├── CliffordAction.lean -- Transported Clifford action on the exterior model
│   ├── SpinRep.lean        -- Restriction of the action to `spinGroup`
│   ├── Chiral.lean         -- Transported chiral decomposition and spin invariance
│   ├── OrthogonalAction.lean -- Ambient spin-vector action and isometry homomorphism
│   ├── CliffordNorm.lean -- Clifford star-norm formulas for vector products
│   ├── ComplexClassification.lean -- Periodicity: complex even/odd matrix models
│   ├── RealClassification.lean -- Periodicity: split `(n,n)` real matrix models + low-signature entries
│   ├── LowDimensional.lean -- Explicit low-dim Clifford models + Spin(2), Spin(3) group IDs
│   ├── Cl60QuaternionMatrix.lean -- Explicit Cl(0,6), Cl(6,0), and sixth-row even Bott entries
│   ├── Cl07RealMatrixProd.lean -- Explicit Cl(0,7) and seventh-row even Bott entries
│   ├── Cl08RealMatrix.lean -- Explicit Cl(0,8) and eighth-row even Bott entries
│   ├── Cl78PositiveEven.lean -- Positive Cl⁺(7,0) and Cl⁺(8,0) even Bott entries
│   ├── TheoremIndex.lean -- Machine-checked paper theorem surface
│   └── OddClassification.lean -- Classification pieces over the odd split form
├── paper/                  -- Submission-ready paper sources (main.tex, refs.bib, README.md)
├── scripts/                -- Reproducibility/verification scripts
├── ROADMAP.md
├── AGENTS.md
└── lakefile.lean
```

## Building

```bash
lake build
```

## Verification and reproducibility

The Lean toolchain is pinned in `lean-toolchain`, and the Mathlib revision is pinned in
`lake-manifest.json`. Pull requests run the full Lean build and proof-hole token check in
GitHub Actions. The same checks can be run locally with:

```bash
bash scripts/verify.sh
```

On Windows PowerShell, use `.\scripts\verify.ps1`.

`THEOREM_INDEX.md` maps the paper's theorem-facing statements to the exact Lean declarations used
to support them.

## References

- Lawson, Michelson — *Spin Geometry* (Princeton, 1989)
- Chevalley — *The Algebraic Theory of Spinors and Clifford Algebras* (Springer, 1996)
- Atiyah, Bott, Shapiro — *Clifford Modules* (Topology, 1964)

## Status

Implemented so far:

- shared Mathlib/notation layer for Clifford, exterior, and quadratic-form work
- totally isotropic subspaces and maximal totally isotropic existence over finite-dimensional fields
- Witt index as the maximal dimension of a totally isotropic subspace
- a canonical maximal-isotropic exterior model `⋀W` with dimension `2 ^ wittIndex`
- the explicit parity splitting `⋀W = ⋀^even W ⊕ ⋀^odd W` for the chosen exterior model
- wedge and contraction operators on the chosen `⋀W` model
- exterior multiplication and contraction flip the chosen even/odd summands
- the split generator action of `W* × W` on `⋀W`, satisfying the hyperbolic Clifford relation
- even split Clifford elements preserve each chosen parity summand, and the restricted split
  spin-group action acts on both halves
- any explicit hyperbolic isometry `Q ≃ dualProd K W` now transports the chosen `⋀W` model to an
  ambient `Cl(V,Q)` action and restricted `spinGroup Q` action
- any explicit hyperbolic presentation `Q ≃ dualProd K W` now also computes the Witt index:
  `wittIndex Q = dim(W)`, via a general bound showing every totally isotropic subspace of
  `dualProd K W` has dimension at most `dim(W)`
- the same explicit hyperbolic presentation also transports the standard split factor `0 × W`
  to a maximal totally isotropic subspace of the ambient quadratic space
- explicit hyperbolic presentations are now packaged as first-class data, carrying their chosen
  `⋀W` spinor model, transported Clifford/spin actions, actual `Module` / `MulAction`
  structures, even/odd halves, Witt-index theorem, and transported maximal isotropic subspace
- a half-dimensional totally isotropic subspace together with a chosen complement now also yields
  such a first-class presentation directly, via
  `QuadraticForm.splitIsometryEquivOfIsCompl` and `HyperbolicPresentation.ofIsCompl`
- more generally, any totally isotropic subspace with a chosen complement now yields a linear
  Witt decomposition `V ≃ W ⊕ W* ⊕ V₀` via
  `QuadraticForm.wittLinearDecompositionOfIsCompl`, together with the residual factor
  `QuadraticForm.wittResidualSubspaceOfIsCompl`; for the canonical chosen Witt subspace, these are
  exposed as `QuadraticForm.wittLinearDecomposition` and `QuadraticForm.wittResidualSubspace`
- that same general chosen-complement setup now also yields the genuine quadratic-form splitting
  `Q ≃ dualProd K W ⊕ Q₀` via `QuadraticForm.wittIsometryEquivOfIsCompl`; for the canonical chosen
  Witt subspace, this is exposed as `QuadraticForm.wittIsometryEquiv`
- that general/canonical Witt splitting is now also packaged through the higher-level presentation
  layer as `Spinor.WittPresentation.ofIsCompl` and `Spinor.WittPresentation.canonical`
- the hyperbolic factor sitting inside the orthogonal complement of the residual term is now exposed
  as `HyperbolicPresentation.wittFactorOfIsCompl` and `HyperbolicPresentation.canonicalWittFactor`,
  so the existing chosen-model Clifford/spin APIs apply directly to that factor too
- when the split isometry is given specifically as `Q ≃ dualProd K Q.wittSubspace`, the canonical
  Witt model now uses that same first-class presentation API and inherits the corresponding
  Clifford/spin module and action structures directly
- in the split-rank Witt-subspace case, the canonical Witt model can now choose a complement
  internally and build its transported Clifford/spin actions directly via `splitWittPresentation`
  and `splitWittSpinRepresentation`
- for nondegenerate finite-dimensional `Q`, the doubled form `Q ⊕ (-Q)` now has a canonical split
  presentation via Mathlib's `QuadraticForm.toDualProd`, upgraded here to an isometry equivalence
  and anchored on the diagonal isotropic subspace of `V × V`
- in that doubled case, the diagonal subspace now realizes the full Witt index and is proved
  maximal totally isotropic
- the doubled canonical split presentation is also exposed as a reusable
  `HyperbolicPresentation (Q ⊕ (-Q))`
- this yields a canonical chosen-model Clifford action, canonical module and spin-group action
  structures, spin representation, and even/odd half-spin spaces for `Q ⊕ (-Q)`, with
  dimensions `2 ^ dim(V)` and `2 ^ (dim(V) - 1)` in positive rank
- in that explicit hyperbolic case, the chosen Witt model now satisfies the expected dimension
  formula `dim = 2 ^ (dim V / 2)`
- for positive Witt index, the chosen even and odd halves of `⋀W` are linearly equivalent and each
  has dimension `2 ^ (dim W - 1)`; hence in the explicit hyperbolic case they have the expected
  half-spin size `2 ^ (dim V / 2 - 1)`
- the induced Clifford action of `Cl(W* × W, dualProd)` on `⋀W` and its restricted split spin-group
  action
- a faithful exterior-model Clifford action obtained from `CliffordAlgebra.equivExterior`
- the induced `spinGroup` representation by restriction
- scalar spin elements are now proved to act trivially on the ambient vector/isometry
  representations and as the matching scalar endomorphisms on the ambient spinor module, yielding a
  reusable non-factorization criterion for the covering-map story whenever a nontrivial scalar spin
  element is available; in particular, if `Q` represents `-1` and `-1 ≠ 1`, the spin
  representation provably cannot factor through the ambient isometry representation, and this is now
  packaged on the canonical chosen-model API as a positive split-rank non-factorization theorem
- any kernel element is now proved to act trivially on the whole Clifford algebra by conjugation,
  hence to commute with every Clifford element
- over domains, the scalar part of the kernel is exactly `±1`, and in the finite-dimensional
  hyperbolic/split setting the chosen-model equivalence `Cl(Q) ≃ End(⋀W)` now forces every kernel
  element to be scalar; hence on the canonical split-rank chosen-model API the ambient
  spin-to-isometry kernel is proved to be exactly `{1, -1}`
- in positive split rank, the full chosen-model spin representation and the nonzero half-spin
  representations are now proved not to factor through the ambient isometry representation, while
  their induced projective actions are packaged as image-subgroup actions on submodules
- the split-line spin image is now identified exactly with the square-scaling subgroup in
  `Spinor.OddClassification`, giving a theorem-level field-sensitive replacement for an
  unrestricted double-cover slogan
- a chiral decomposition `S = S⁺ ⊕ S⁻` transported from Clifford parity, with `spinGroup`
  preserving both summands and restricting to actions on each summand
- on the zero-form chosen model `⋀W`, an identification of the abstract chiral pieces with the
  explicit even/odd exterior summands `⋀^even W` and `⋀^odd W`
- in the split model, `splitCliffordAction : Cl(W* × W, dualProd) → End(⋀W)` is now proved
  surjective and injective by explicit basis projectors / matrix units
- through `HyperbolicPresentation`, `wittPresentation`, and `splitWittPresentation`, a chosen-model
  positive/negative chiral API on `⋀W` identified with those even/odd summands, carrying the
  corresponding even-Clifford and restricted spin representations, and inheriting the transported
  simplicity / inequivalence statements under those positive/negative names
- in split rank, that canonical Witt-model half-spin surface is also exposed directly through the
  top-level aliases `splitSpinorModule`, `positiveHalfSpinorModule`, and `negativeHalfSpinorModule`,
  together with their canonical Clifford / spin actions and the corresponding simplicity /
  inequivalence results
- through those same presentation APIs, the transported chosen-model Clifford action on `⋀W` is
  now proved faithful in the explicit hyperbolic, Witt, and split-Witt settings
- in the explicit hyperbolic case, that chosen-model Clifford action is now packaged as an algebra
  equivalence `Cl(Q) ≃ End(⋀W)` and hence as a concrete matrix-algebra model; the same
  endomorphism-algebra equivalence is exposed through the Witt and split-Witt presentation APIs
- in split rank, the canonical Witt-model Clifford algebra is now packaged as a full matrix algebra
  `Cl(Q) ≃ Mat_(2^(dim V / 2))(K)` through `splitWittCliffordEquivMatrix`
- in the split model, the full Clifford module `⋀W` is now simple, and that simplicity is
  transported to the explicit hyperbolic, Witt, and split-Witt chosen-model presentations
- in the split model, the chosen even half `⋀^even W` is simple under the even Clifford algebra,
  and in positive split rank the same is true for `⋀^odd W`; this half-spin simplicity is also
  transported to the explicit hyperbolic, Witt, and split-Witt chosen-model presentations
- the chosen even and odd halves are now also proved inequivalent as modules over the even
  Clifford algebra in the split model, and that inequivalence is transported to the explicit
  hyperbolic, Witt, and split-Witt chosen-model presentations
- the even Clifford algebra itself is now packaged on those chosen half-spin modules as
  `Cl⁺(Q) ≃ End(⋀^even W) × End(⋀^odd W)` in the explicit hyperbolic case, with Witt and
  split-Witt wrappers and, in positive split rank, a concrete product-of-matrices form of size
  `2^(dim V / 2 - 1)` on each factor
- via `CliffordAlgebra.equivEven`, the standard odd split form `H(W) ⊕ ⟨1⟩` is now also packaged as
  `Cl(H(W) ⊕ ⟨1⟩) ≃ Mat_(2^dim W)(K) × Mat_(2^dim W)(K)`
- over `ℂ`, the standard even-dimensional sum-of-squares form on `Fin n ⊕ Fin n` is now packaged as
  `Cl(2n, ℂ) ≃ Mat_(2^n)(ℂ)` in `Spinor.complexEvenCliffordEquivMatrix`
- over `ℂ`, the corresponding odd-dimensional grouped sum-of-squares form is now packaged as
  `Cl(2n+1, ℂ) ≃ Mat_(2^n)(ℂ) × Mat_(2^n)(ℂ)` in
  `Spinor.complexOddCliffordEquivProdMatrix`
- the low-dimensional files now record explicit specializations of those algebraic models,
  including `Cl(1, ℂ) ≃ ℂ × ℂ`, `Cl(2, ℂ) ≃ Mat₂(ℂ)`, `Cl(3, ℂ) ≃ Mat₂(ℂ) × Mat₂(ℂ)`,
  `Cl(4, ℂ) ≃ Mat₄(ℂ)`, `Cl(0,1) ≃ ℂ`, `Cl(0,2) ≃ ℍ`, `Cl(2,0) ≃ Mat₂(ℝ)`,
  `Cl⁺(2,0) ≃ ℂ`, `Cl(3,0) ≃ Mat₂(ℂ)`,
  `Cl⁺(3,0) ≃ ℍ`, `Cl(0,4) ≃ Mat₂(ℍ)`, `Cl(4,0) ≃ Mat₂(ℍ)`,
  `Cl⁺(4,0) ≃ ℍ × ℍ`, `Cl⁺(0,5) ≃ Mat₂(ℍ)`, `Cl(0,5) ≃ Mat₄(ℂ)`,
  `Cl⁺(5,0) ≃ Mat₂(ℍ)`,
  `Cl(5,0) ≃ Mat₂(ℍ) × Mat₂(ℍ)`,
  `Cl⁺(0,6) ≃ Mat₄(ℂ)`, `Cl(0,6) ≃ Mat₈(ℝ)`,
  `Cl⁺(6,0) ≃ Mat₄(ℂ)`, `Cl(6,0) ≃ Mat₄(ℍ)`,
  `Cl⁺(0,7) ≃ Mat₈(ℝ)`, `Cl(0,7) ≃ Mat₈(ℝ) × Mat₈(ℝ)`,
  `Cl⁺(0,8) ≃ Mat₈(ℝ) × Mat₈(ℝ)`, `Cl(0,8) ≃ Mat₁₆(ℝ)`,
  `Cl⁺(7,0) ≃ Mat₈(ℝ)`, `Cl⁺(8,0) ≃ Mat₈(ℝ) × Mat₈(ℝ)`,
  `Cl(1,1) ≃ Mat₂(ℝ)`,
  `Cl⁺(1,1) ≃ ℝ × ℝ`, `Cl(2,2) ≃ Mat₄(ℝ)`, and
  `Cl⁺(2,2) ≃ Mat₂(ℝ) × Mat₂(ℝ)`
- `Spinor.LowDimensional` now also packages the first compact low-dimensional group
  identifications:
  `realSpin02EquivUnitaryComplex : spinGroup realCl02Form ≃* unitary ℂ` and
  `realSpin03EquivUnitaryQuaternion : spinGroup realCl03Form ≃*
  unitary ℍ[ℝ, -1, -1]`,
  i.e. `Spin(2) ≃ U(1)` and `Spin(3) ≃ SU(2)` in Mathlib's negative-signature convention
- over `ℝ`, the standard split-signature form `(n,n)` is now packaged as
  `Cl(n,n) ≃ Mat_(2^n)(ℝ)` in `Spinor.realSplitCliffordEquivMatrix`,
  with the first explicit base case `Cl(1,1) ≃ Mat₂(ℝ)` recorded as
  `Spinor.realClifford_1_1_equivMatrix2`
- over `ℝ`, the corresponding even split Clifford algebra is now packaged as
  `Cl⁺(n,n) ≃ Mat_(2^(n-1))(ℝ) × Mat_(2^(n-1))(ℝ)` in
  `Spinor.realSplitEvenCliffordEquivProdMatrix`
- `Spinor.OrthogonalAction` now packages the ambient vector action
  `spinLinearRepresentation : spinGroup Q → (M ≃ₗ[R] M)` obtained from conjugation on the Clifford
  copy `ι(Q)(M)`, proves this action preserves `Q` via `spinVector_preserves_quadratic`, and
  packages each spin element as an ambient isometry `spinIsometryEquiv : Q.IsometryEquiv Q`
  together with the full homomorphism
  `spinIsometryRepresentation : spinGroup Q →* Q.IsometryEquiv Q`
- `Spinor.HyperbolicAction` now proves the Levi-projective exterior-action theorem with a unit
  scalar, via
  `splitCliffordAction_eq_units_smul_exteriorMap_of_spinSpecialOrthogonalRepresentation_eq`, and
  packages explicit transvection Clifford units, chosen-line square-scaling lifts, and the
  square-determinant Levi factorization/lift, determinant-square necessity theorem, and exact
  finite-basis split-Levi spin-image iff API used by the paper; the same theorem surface now
  exposes the determinant square-class homomorphisms
  `linearEquivDetSquareClassHom` and `dualProdLeviDetSquareClassHom`; both are surjective onto
  the square-class quotient once a basis line is chosen, and their kernels are exactly the
  pulled-back and canonical packaged split-Levi spin images by
  `linearEquivDetSquareClassHom_surjective`,
  `linearEquivDetSquareClassHom_ker_eq_spin_image_subgroup`,
  `dualProdLeviDetSquareClassHom_surjective` and
  `dualProdLeviDetSquareClassHom_ker_eq_spin_image_comap`; the first-isomorphism-theorem wrapper
  `linearEquivSpinImageQuotientEquivSquareClass` gives the linear-coordinate quotient, while
  `dualProdLeviSpinImageQuotientEquivSquareClass` identifies the split Levi subgroup modulo its
  spin-image subgroup with the square-class quotient; the aliases
  `linearEquivSplitLeviSpinorNormHom` and `dualProdLeviSpinorNormHom` expose this proved
  finite-basis split-Levi character under spinor-norm-facing names without claiming a full
  orthogonal-group spinor-norm API
- `Spinor.CliffordNorm` now packages the global Clifford-level product formula
  `star_cliffordVectorProduct_mul_cliffordVectorProduct`, identifying
  `star (ι v₁ ... ι vₙ) * (ι v₁ ... ι vₙ)` with the scalar product of the signed quadratic
  values, together with the invertible-vector unit and square-class forms
  `cliffordInvertibleVectorProductNormUnit` and
  `cliffordInvertibleVectorProductSpinorNormClass`; the scalar, unit, and square-class products
  are invariant under list permutation and reversal via
  `cliffordVectorProductNormScalar_perm`,
  `cliffordInvertibleVectorProductNormUnit_perm`, and
  `cliffordInvertibleVectorProductSpinorNormClass_perm`, and inserting a repeated invertible
  vector pair, duplicating an invertible-vector product/contiguous subproduct, or repeating a
  subproduct with intervening factors is square-class-trivial via
  `cliffordInvertibleVectorProductSpinorNormClass_append_cons_self_cons`,
  `cliffordInvertibleVectorProductSpinorNormClass_append_append_self_append`, and
  `cliffordInvertibleVectorProductSpinorNormClass_append_append_middle_self_append`; this is a
  reflection-product substrate, not an independence theorem for arbitrary orthogonal decompositions
- the split hyperbolic line is now theorem-complete: the spin image is exactly the square-scaling
  subgroup, the spin map onto `SO(1,1)` is surjective iff the square map on `Kˣ` is surjective, and
  a nonsquare unit gives a formal non-surjectivity theorem; over algebraically closed fields,
  `units_square_surjective_of_isAlgClosed` specializes this to full split-line double-cover and
  finite-basis split-Levi lift/image corollaries

- the ambient chiral identification is now closed: the canonical chosen-model positive and
  negative half-spin modules are, by construction, the ambient `positiveChiral` /
  `negativeChiral` submodules of the zero-form regular spinor module on `Q.wittSubspace`; see
  `Spinor.Presentation.positiveHalfSpinorModule_eq_ambient_positiveChiral`,
  `Spinor.Presentation.negativeHalfSpinorModule_eq_ambient_negativeChiral`, and the
  packaged bundle `Spinor.Presentation.splitSpinor_chiral_correspondence`, which chains through
  the `evenWittExterior` / `oddWittExterior` identifications to give the full
  `S⁺ = ⋀^even W`, `S⁻ = ⋀^odd W` roadmap statement (Phase 3.2)
- `Spinor.Presentation` exposes the canonical split-rank capstones
  `splitSpinorModule_finrank`, `positiveHalfSpinorModule_finrank`,
  `negativeHalfSpinorModule_finrank` (dimension formula, Phase 2.3),
  `splitSpinorCliffordAction_sq_apply` (top-level Clifford relation, Phase 2.2), and
  `splitSpinorCliffordAction_injective` (top-level faithfulness, Phase 2.2)
- `Spinor.RealClassification` now also records the canonical low-signature entries
  `cl_n_n_equivMatrix`, `cl_n_n_even_equivProdMatrix`, and
  `cl_succ_n_n_equivProdMatrix` for the split `Cl(n,n)`, even split `Cl⁺(n,n)`,
  and grouped odd split `Cl(n+1,n)` rows,
  `cl_0_0_equivReal : Cl(0,0) ≃ₐ[ℝ] ℝ`,
  `cl_1_0_equivRealProd : Cl(1,0) ≃ₐ[ℝ] ℝ × ℝ`,
  `cl_1_0_even_equivReal : Cl⁺(1,0) ≃ₐ[ℝ] ℝ`,
  `cl_0_1_equivComplex : Cl(0,1) ≃ₐ[ℝ] ℂ`,
  `cl_0_1_even_equivReal : Cl⁺(0,1) ≃ₐ[ℝ] ℝ`,
  `cl_0_2_equivQuaternion : Cl(0,2) ≃ₐ[ℝ] ℍ[ℝ, -1, -1]`,
  `cl_0_2_even_equivComplex : Cl⁺(0,2) ≃ₐ[ℝ] ℂ`,
  `cl_2_0_equivMatrix2 : Cl(2,0) ≃ₐ[ℝ] Mat₂(ℝ)`,
  `cl_2_0_even_equivComplex : Cl⁺(2,0) ≃ₐ[ℝ] ℂ`,
  `cl_3_0_equivComplexMatrix2 : Cl(3,0) ≃ₐ[ℝ] Mat₂(ℂ)`,
  `cl_3_0_even_equivQuaternion : Cl⁺(3,0) ≃ₐ[ℝ] ℍ`,
  `cl_0_3_equivQuaternionProd : Cl(0,3) ≃ₐ[ℝ] ℍ × ℍ`,
  `cl_0_3_even_equivQuaternion : Cl⁺(0,3) ≃ₐ[ℝ] ℍ`,
  `cl_0_4_equivQuaternionMatrix2 : Cl(0,4) ≃ₐ[ℝ] Mat₂(ℍ)`,
  `cl_0_4_even_equivQuaternionProd : Cl⁺(0,4) ≃ₐ[ℝ] ℍ × ℍ`,
  `cl_0_5_even_equivQuaternionMatrix2 : Cl⁺(0,5) ≃ₐ[ℝ] Mat₂(ℍ)`,
  `cl_0_5_equivComplexMatrix4 : Cl(0,5) ≃ₐ[ℝ] Mat₄(ℂ)`,
  `cl_4_0_equivQuaternionMatrix2 : Cl(4,0) ≃ₐ[ℝ] Mat₂(ℍ)`,
  `cl_4_0_even_equivQuaternionProd : Cl⁺(4,0) ≃ₐ[ℝ] ℍ × ℍ`,
  `cl_5_0_even_equivQuaternionMatrix2 : Cl⁺(5,0) ≃ₐ[ℝ] Mat₂(ℍ)`,
  `cl_5_0_equivQuaternionMatrix2Prod : Cl(5,0) ≃ₐ[ℝ] Mat₂(ℍ) × Mat₂(ℍ)`,
  `cl_0_6_even_equivComplexMatrix4 : Cl⁺(0,6) ≃ₐ[ℝ] Mat₄(ℂ)`,
  `cl_0_6_equivMatrix8 : Cl(0,6) ≃ₐ[ℝ] Mat₈(ℝ)`,
  `cl_6_0_even_equivComplexMatrix4 : Cl⁺(6,0) ≃ₐ[ℝ] Mat₄(ℂ)`,
  `cl_6_0_equivQuaternionMatrix4 : Cl(6,0) ≃ₐ[ℝ] Mat₄(ℍ)`,
  `cl_0_7_even_equivMatrix8 : Cl⁺(0,7) ≃ₐ[ℝ] Mat₈(ℝ)`,
  `cl_0_7_equivMatrix8Prod : Cl(0,7) ≃ₐ[ℝ] Mat₈(ℝ) × Mat₈(ℝ)`,
  `cl_0_8_even_equivMatrix8Prod : Cl⁺(0,8) ≃ₐ[ℝ] Mat₈(ℝ) × Mat₈(ℝ)`,
  `cl_0_8_equivMatrix16 : Cl(0,8) ≃ₐ[ℝ] Mat₁₆(ℝ)`,
  `cl_7_0_even_equivMatrix8 : Cl⁺(7,0) ≃ₐ[ℝ] Mat₈(ℝ)`,
  and `cl_8_0_even_equivMatrix8Prod :
  Cl⁺(8,0) ≃ₐ[ℝ] Mat₈(ℝ) × Mat₈(ℝ)`,
  plus the split entries
  `cl_1_1_equivMatrix2`, `cl_1_1_even_equivRealProd`, `cl_2_2_equivMatrix4`, and
  `cl_2_2_even_equivProdMatrix2`, extending the packaged low-signature portion of
  the Bott periodicity table (Phase 4.1)
- `Spinor.Cl03QuaternionProd` now packages the compact quaternionic identification
  `realSpin04EquivUnitaryQuaternionPair :
  spinGroup realCl04Form ≃* unitary ℍ[ℝ, -1, -1] × unitary ℍ[ℝ, -1, -1]`,
  together with the surjective forward map
  `spinGroupRealCl04ToUnitaryQuaternionPair`, the diagonal constructor
  `unitaryQuaternionToSpinGroupRealCl04Diagonal`, and the full anti-diagonal constructor
  `unitaryQuaternionToSpinGroupRealCl04Antidiagonal` (Phase 4.2)
- `Spinor.TheoremIndex` is a machine-checked paper theorem surface: it imports and `#check`s the
  declarations cited by `THEOREM_INDEX.md`, so theorem-name drift is caught by `lake build`
- `paper/` now contains submission-ready sources (`main.tex`, `refs.bib`, `README.md`) grounded
  in the formalized theorem package, with target venues recorded for CPP 2027 / ITP 2027 /
  *Advances in Applied Clifford Algebras* (Phase 5.1)

Explicit scope boundaries for this algebraic submission package:

- the full Bott period-8 table beyond the split foundation and packaged low-signature entries
  through `Cl(0,3)`, `Cl(0,4)`, `Cl(0,5)`, `Cl(0,6)`, `Cl(0,7)`, `Cl(0,8)`,
  `Cl(3,0)`,
  `Cl(4,0)`, `Cl(5,0)`, and `Cl(6,0)`, selected even positive/negative companions
  through `Cl⁺(0,8)` and `Cl⁺(8,0)`, and the explicit `Cl(2,2)` / `Cl⁺(2,2)`
  split entries
- a full all-orthogonal-group image classification beyond the packaged split-rank kernel,
  non-factorization, projective descent, exact split-line iff criterion, exact finite-basis
  split-Levi spin-image iff theorem, and onto split-Levi determinant square-class quotient
  character / quotient isomorphism with its split-Levi spinor-norm-facing wrappers and the
  global Clifford-level vector-product norm formula with product-order invariance, repeated-pair
  square-class cancellation, and duplicated-product/subproduct square-class triviality, including
  separated repeated subproducts
- a full global orthogonal-group spinor-norm theory beyond the product-level Clifford norm and
  finite-basis split-Levi square-class APIs

The library currently has a clean `lake build` and zero `sorry` / `admit`.
