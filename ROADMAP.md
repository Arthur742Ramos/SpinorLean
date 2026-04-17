# SpinorLean — Roadmap

## Goal
First-ever formalization of spinor representations from Clifford algebras in a proof assistant.
Target venues: CPP 2027, ITP 2027, or *Advances in Applied Clifford Algebras*.

---

## Phase 1: Foundations (Week 1-2)

### 1.1 Project Setup
- [x] Lean 4 + Mathlib project via `lake init`
- [x] Verify Mathlib's `CliffordAlgebra`, `ExteriorAlgebra`, `SpinGroup` imports compile
- [x] Establish notation and convention file

### 1.2 Quadratic Spaces & Isotropic Subspaces
- [x] Define totally isotropic subspaces of a quadratic module (V, Q)
- [x] Prove existence of maximal isotropic subspaces for finite-dimensional spaces over fields
- [x] Witt decomposition: V ≅ W ⊕ W* ⊕ V₀ (hyperbolic splitting)
  - [x] Package the underlying linear decomposition `V ≃ W ⊕ W* ⊕ V₀` from a chosen
    complement, with canonical `wittSubspace` specializations and residual-dimension formulas
  - [x] Upgrade that linear decomposition to the orthogonal / hyperbolic quadratic-form splitting
  - [x] Package the resulting general quadratic Witt splitting as first-class presentation data and
    expose its orthogonal hyperbolic factor through the existing chosen-model APIs
- [x] Package the chosen-model transport once an explicit hyperbolic isometry `Q ≃ dualProd K W` is given
- [x] Prove any explicit hyperbolic presentation `Q ≃ dualProd K W` satisfies `wittIndex Q = dim W`
- [x] Package the maximal totally isotropic subspace determined by an explicit hyperbolic
  presentation `Q ≃ dualProd K W`
- [x] From a half-dimensional totally isotropic subspace `W` plus a chosen complement `U`,
  construct an explicit split isometry `Q ≃ dualProd K W`
- [x] In the nondegenerate doubled case, package the canonical split presentation
  `(Q.prod (-Q)) ≃ dualProd K Δ` using the diagonal isotropic subspace `Δ ≤ V × V`
- [x] In the doubled canonical split case, prove the diagonal subspace `Δ` realizes the Witt index
  and is maximal totally isotropic
- [x] Witt index and its basic properties

### 1.3 Mathlib Inventory
- [x] Audit `Mathlib.LinearAlgebra.CliffordAlgebra.*` — catalog what's available
- [x] Audit `Mathlib.LinearAlgebra.ExteriorAlgebra.*` — same
- [x] Audit `Mathlib.LinearAlgebra.QuadraticForm.*` — isotropic subspace API
- [x] Document gaps that need filling

---

## Phase 2: The Spinor Module (Week 2-4)

### 2.1 Exterior Algebra of Maximal Isotropic Subspace
- [x] Given W ≤ V maximal isotropic, construct ⋀W (exterior algebra on W)
- [x] Show dim(⋀W) = 2^n where n = dim(W) = Witt index

### 2.2 Clifford Action on ⋀W
- [x] Define the split hyperbolic action of `Cl(W* × W, dualProd)` on `⋀W`
- [x] Restrict that split hyperbolic action to `spinGroup (dualProd)`
- [ ] Define the left action of Cl(V, Q) on ⋀W
  - [x] Transport the split action along an explicit hyperbolic isometry `Q ≃ dualProd K W`
  - [x] Package explicit hyperbolic presentations `Q ≃ dualProd K W` as first-class chosen-model
    spinor data
  - [x] Expose those presented chosen models as actual `Module (CliffordAlgebra Q)` and
    `MulAction (spinGroup Q)` structures, including the canonical doubled case
  - [x] Package the chosen Witt-subspace case `Q ≃ dualProd K Q.wittSubspace` through the same
    presentation API
  - [x] Package the split-data case `(W,U)` through the same transport/presentation API
  - [x] In split rank, let the canonical Witt-subspace model choose a complement internally and
    build the transported action without an explicit isometry argument
  - [x] Specialize that transport canonically to the doubled form `Q ⊕ (-Q)` in the nondegenerate case
  - [x] Derive that isometry canonically from a full Witt decomposition `V ≃ W ⊕ W* ⊕ V₀`
  - [x] For `w ∈ W`, the split generator action is exterior multiplication via `wedgeAction`
  - [x] For `f ∈ W*`, the split generator action is interior multiplication / contraction via
    `contractionAction`
  - [x] Extend the split generator action to all of `Cl(W* × W, dualProd)` via
    `splitCliffordAction`, then transport it along the explicit hyperbolic presentation API
  - [ ] Remaining gap: a presentation-free non-split action on plain `⋀W` is not yet packaged
- [ ] Prove this action satisfies the Clifford relation: a(v) ∘ a(v) = Q(v) · id
  - [x] In the transported hyperbolic case, prove the vector relation on `⋀W`
  - [x] Package the same vector relation on the Witt-presentation and split-Witt chosen-model APIs
  - [x] Top-level canonical split-rank capstone: `splitSpinorCliffordAction_sq_apply`
  - [ ] Remaining gap: the theorem-facing statement is still confined to the split/hyperbolic
    presentation surfaces above
- [ ] Prove ⋀W is a faithful Cl(V,Q)-module (for non-degenerate Q)
  - [x] In the split model, show `splitCliffordAction : Cl(W* × W, dualProd) → End(⋀W)` is
    surjective and injective
  - [x] Transport that faithfulness to explicit hyperbolic presentations `Q ≃ dualProd K W`,
    the Witt-presentation API, and the split-rank canonical Witt model
  - [x] Top-level canonical split-rank capstone: `splitSpinorCliffordAction_injective`
  - [ ] Remaining gap: there is still no presentation-free top-level `⋀W` API for arbitrary
    non-split forms

### 2.3 The Spinor Module
- [ ] **Define `SpinorModule Q` := ⋀W as a `Module (CliffordAlgebra Q)`**
  - [x] The current top-level alias in `Spinor.Basic` is the ambient regular model
    `SpinorModule Q := ExteriorAlgebra R M`
  - [x] `Spinor.CliffordAction` equips that ambient model with a faithful
    `Module (CliffordAlgebra Q)` structure
  - [x] The chosen-model `⋀W` surfaces are packaged separately through
    `HyperbolicPresentation.spinorModule`, `WittExteriorModel`, and `splitSpinorModule`
  - [ ] Remaining gap: there is still no single theorem-facing top-level alias replacing the
    ambient regular model by the chosen maximal-isotropic one
- [ ] Prove irreducibility (for algebraically closed fields, even dimension)
  - [x] In the split model, prove the full Clifford module `⋀W` is simple
  - [x] Transport that simplicity to the explicit hyperbolic, Witt, and split-Witt presentation APIs
- [ ] Prove the dimension formula: dim(S) = 2^(n/2)
  - [x] In the explicit hyperbolic case `Q ≃ dualProd K W`, show `dim(⋀W) = 2 ^ (dim V / 2)`
  - [x] Top-level canonical split-rank capstones: `splitSpinorModule_finrank`,
    `positiveHalfSpinorModule_finrank`, `negativeHalfSpinorModule_finrank`

---

## Phase 3: Spin Group Action (Week 4-5)

### 3.1 Restriction to Spin Group
- [x] Show `spinGroup Q` acts on `SpinorModule Q` by restriction of Clifford action
- [x] This gives the **spin representation**: `spinGroup Q →* (SpinorModule Q →ₗ SpinorModule Q)`
- [x] Prove this is a group homomorphism

### 3.2 Half-Spin / Chiral Representations (even dimension)
- [x] Use the ℤ/2-grading of Cl(V,Q) to decompose S = S⁺ ⊕ S⁻
- [x] Define the chosen-model splitting `⋀W = ⋀^even W ⊕ ⋀^odd W`
- [x] Identify the zero-form chiral pieces on the chosen `⋀W` model with `⋀^even W` and `⋀^odd W`
- [x] Package the chosen-model positive/negative chiral halves and their restricted spin
  representations through the hyperbolic/Witt presentation APIs
- [x] Prove the split hyperbolic spin action on the chosen `⋀W` model preserves `⋀^even W` and `⋀^odd W`
- [x] In positive split rank, prove the chosen even and odd halves have equal dimension
- [x] Identify these chosen even/odd summands with the ambient chiral modules `S⁺` and `S⁻`
  - `Spinor.Presentation.positiveHalfSpinorModule_eq_ambient_positiveChiral`,
    `Spinor.Presentation.negativeHalfSpinorModule_eq_ambient_negativeChiral` identify the
    chosen-model `S⁺`/`S⁻` with the ambient `positiveChiral`/`negativeChiral` construction applied
    to the zero form on `Q.wittSubspace`; combined with
    `Spinor.Presentation.positiveHalfSpinorModule_eq_evenWittExterior` and
    `Spinor.Presentation.negativeHalfSpinorModule_eq_oddWittExterior` (and the packaged
    `Spinor.Presentation.splitSpinor_chiral_correspondence`), this gives the identification with
    `⋀^even W` / `⋀^odd W`. `Spinor.Presentation.positiveHalfSpinorModuleLinearEquivEvenWittExterior`
    and `Spinor.Presentation.negativeHalfSpinorModuleLinearEquivOddWittExterior` provide the
    by-product `K`-linear equivalences.
- theorem-facing half-spin API now uses the canonical chosen-model wrappers in
  `Spinor.Presentation`
- [x] Prove Spin(V,Q) preserves the decomposition (Weyl spinors)
- [x] Prove the theorem-facing canonical `S⁺` and `S⁻` modules are irreducible and inequivalent
  (for dim ≥ 4)
  - [x] In the split model, prove `⋀^even W` is simple under the even Clifford algebra and, in
    positive split rank, prove the same for `⋀^odd W`
  - [x] Transport that half-spin simplicity to the explicit hyperbolic, Witt, and split-Witt
    presentation APIs
  - [x] Prove the chosen-model inequivalence statement and transport it to the explicit
    hyperbolic, Witt, and split-Witt presentation APIs
  - [x] Package the top-level canonical chosen-model `S⁺` / `S⁻` version via
    `positiveHalfSpinorModule`, `negativeHalfSpinorModule`, and the corresponding
    simplicity/inequivalence wrappers

---

## Phase 4: Key Theorems (Week 5-7)

### 4.1 Periodicity & Classification
- [x] For any explicit hyperbolic presentation `Q ≃ dualProd K W`, package the chosen-model
  Clifford action as an algebra equivalence `Cl(Q) ≃ End(⋀W)` and hence as a matrix-algebra model
- [x] Expose the corresponding endomorphism-algebra equivalence through the Witt and split-Witt
  presentation APIs
- [x] In split rank, package the canonical Witt-model Clifford algebra as a full matrix algebra of
  size `2^(dim V / 2)`
- [x] For any explicit hyperbolic presentation `Q ≃ dualProd K W`, package the even Clifford
  algebra as `Cl⁺(Q) ≃ End(⋀^even W) × End(⋀^odd W)`
- [x] Expose the corresponding even-Clifford product-endomorphism equivalence through the Witt and
  split-Witt presentation APIs
- [x] In split rank and positive Witt index, package the canonical even Clifford algebra as
  `Mat_(2^(dim V / 2 - 1))(K) × Mat_(2^(dim V / 2 - 1))(K)`
- [x] Package the standard odd split form `H(W) ⊕ ⟨1⟩` as
  `Mat_(2^dim W)(K) × Mat_(2^dim W)(K)` via `CliffordAlgebra.equivEven`
- [x] Cl(n, ℂ) ≅ Mat(2^(n/2), ℂ) for n even
  - implemented as `Spinor.ComplexClassification.complexEvenCliffordEquivMatrix`, i.e. the standard
    `2n`-dimensional complex sum-of-squares form on `Fin n ⊕ Fin n`
- [x] Cl(n, ℂ) ≅ Mat(2^((n-1)/2), ℂ) × Mat(2^((n-1)/2), ℂ) for n odd
  - implemented as `Spinor.ComplexClassification.complexOddCliffordEquivProdMatrix`, i.e. the
    standard grouped form consisting of the even `2n` sum-of-squares block plus one extra square
- [ ] Bott periodicity for real Clifford algebras (period 8)
  - foundation now started in `Spinor.RealClassification`: standard signature forms are packaged,
  `Cl(1,1) ≃ Mat₂(ℝ)` is explicit, and more generally the split forms `Cl(n,n)` are packaged as
  `Mat_(2^n)(ℝ)` with even part
  `Cl⁺(n,n) ≃ Mat_(2^(n-1))(ℝ) × Mat_(2^(n-1))(ℝ)`;
  the grouped odd split-signature row `Cl(n+1,n)` is now also packaged as
  `Spinor.realOddSplitPositiveCliffordEquivProdMatrix`, i.e.
  `Mat_(2^n)(ℝ) × Mat_(2^n)(ℝ)`;
  canonical low-signature entries `Spinor.RealClassification.cl_0_1_equivComplex`
  (`Cl(0,1) ≃ ℂ`) and `Spinor.RealClassification.cl_0_2_equivQuaternion`
  (`Cl(0,2) ≃ ℍ`) are now packaged as first-class algebra isomorphisms in the
  `Spinor.RealClassification` namespace, starting the negative-definite row of the
  real classification table

### 4.2 Low-Dimensional Examples
- [x] Spin(2) ≃ U(1) (circle)
  - packaged as
    `Spinor.LowDimensional.realSpin02EquivUnitaryComplex : spinGroup realCl02Form ≃* unitary ℂ`
    using Mathlib's compact negative-signature normalization
- [x] Spin(3) ≃ SU(2) (unit quaternions / Pauli matrices)
  - packaged as
    `Spinor.LowDimensional.realSpin03EquivUnitaryQuaternion :
    spinGroup realCl03Form ≃* unitary ℍ`,
    using the explicit factorization of every unit quaternion into a product of two
    unit 3-vectors in `Cl⁺(0,3)`
- [x] Spin(4) → SU(2) × SU(2)
  - scaffolding: `Spinor.LowDimensional.realCl04Form` (negative-signature 4-form) and
    `Spinor.LowDimensional.realEvenCl04EquivCl03 : Cl⁺(0,4) ≃ₐ[ℝ] Cl(0,3)` via
    `CliffordAlgebra.equivEven`; the classical `Cl⁺(0,4) ≃ ℍ × ℍ` is now packaged as
    `Spinor.realEvenCl04EquivQuaternionProd` in `Spinor.Cl03QuaternionProd`,
    composed from `realEvenCl04EquivCl03` and `realCl03EquivQuaternionProd`; the
    group-level forward map is now packaged as
    `Spinor.spinGroupRealCl04ToUnitaryQuaternionPair :
    spinGroup realCl04Form →* unitary ℍ × unitary ℍ` with injective theorem
    `Spinor.spinGroupRealCl04ToUnitaryQuaternionPair_injective`, surjective theorem
    `Spinor.spinGroupRealCl04ToUnitaryQuaternionPair_surjective`, and final equivalence
    `Spinor.realSpin04EquivUnitaryQuaternionPair`; an explicit
    diagonal compact subgroup is now also packaged via
    `Spinor.unitaryQuaternionToSpinGroupRealCl04Diagonal` together with
    `Spinor.spinGroupRealCl04ToUnitaryQuaternionPair_apply_diag_preimage`; the
    full anti-diagonal subgroup is now also packaged via
    `Spinor.unitaryQuaternionToSpinGroupRealCl04Antidiagonal` together with
    `Spinor.spinGroupRealCl04ToUnitaryQuaternionPair_apply_antidiag_preimage`,
    and arbitrary pairs are lifted explicitly by
    `Spinor.spinGroupRealCl04ToUnitaryQuaternionPair_apply_preimage`
- [x] These connect spinors to familiar physics
  - foundation now includes explicit low-dimensional Clifford-algebra models in
    `Spinor.LowDimensional`, including complex `Cl(1)`, `Cl(2)`, `Cl(3)`, `Cl(4)`, real
    `Cl(0,1) ≃ ℂ`, `Cl(0,2) ≃ ℍ`, `Cl⁺(2,0) ≃ ℂ`, `Cl⁺(3,0) ≃ ℍ`, and split-real
    `Cl(1,1)`, `Cl⁺(1,1)`, `Cl(2,2)`, `Cl⁺(2,2)`; the first group-level compact identification
    layer now packages `Spin(2) ≃ U(1)`, `Spin(3) ≃ SU(2)`, and
    `Spin(4) ≃ SU(2) × SU(2)`, leaving the higher low-dimensional
    Spin-identification layer (starting with `Spin(5)`)

### 4.3 The Covering Map
- [ ] Upgrade the ambient isometry representation to a packaged double cover `Spin(V,Q) → SO(V,Q)`
  - [x] package the ambient vector action
    `Spinor.spinLinearRepresentation : spinGroup Q → (V ≃ₗ[R] V)` by conjugation on
    `CliffordAlgebra.ι Q`, and prove each spin element preserves `Q` via
    `Spinor.spinVector_preserves_quadratic` / `Spinor.spinIsometryEquiv`
  - [x] package those ambient isometries as a genuine homomorphism
    `Spinor.spinIsometryRepresentation : spinGroup Q →* Q.IsometryEquiv Q`
  - [x] package the special orthogonal target as
    `QuadraticForm.specialOrthogonalGroup`
  - [x] prove the determinant-one statement
    `Spinor.spinLinearRepresentation_det_eq_one`
  - [x] factor the ambient action through that target as
    `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional`
  - [x] identify the finite-dimensional nondegenerate kernel as `{1, -1}` via
    `Spinor.spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one`
  - [x] reduce surjectivity to a concrete generator theorem via
    `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_of_pairGeneratorClosure_eq_top`
  - [ ] Remaining gap: prove the canonical two-reflection lifts
    `Spinor.spinSpecialOrthogonalPairGeneratorSet` generate `SO(V,Q)`
- [x] Kernel of the ambient spin-to-isometry map is `{1, -1}` in finite-dimensional
  nondegenerate rank
  - done on the ambient API by
    `Spinor.spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one`, extending the earlier
    split/hyperbolic chosen-model theorem `splitSpinorCoveringKernel_eq_one_or_neg_one`
  - the remaining open part of the covering-map package is surjectivity / double-cover packaging
- [ ] The spin representation does NOT factor through the ambient isometry representation
  - [x] in the ambient regular model, if `Q` represents `-1` and `-1 ≠ 1`, package
    `spinRepresentation_not_factor_through_isometry_of_exists_quadratic_eq_neg_one`
  - done in positive split rank on the canonical chosen-model API via
    `splitSpinorRepresentation_not_factor_through_isometry`; the fully general covering-map
    formulation remains open

---

## Phase 5: Paper & Polish (Week 7-8)

### 5.1 Paper Writing
- paper draft now lives at `paper/` (`main.tex`, `refs.bib`, `README.md`) with
  substantive prose tied to the current repository state; it is now a working
  draft rather than mere scaffolding, though polishing and final exposition
  remain
- [x] Introduction: why spinors matter, why formalization is novel
- [x] Related work: lean-ga, Mathlib Clifford, what's missing
- [x] Formalization architecture
- [x] Key proof highlights (the hard parts)
- [x] Lessons learned & Mathlib gaps discovered
- [x] Future work: spinor bundles, Dirac operators

### 5.2 Code Quality
- [x] Full `lake build` clean
- [x] Zero `sorry` / `admit` sweep
- [ ] Mathlib-compatible style
- [x] Module documentation (Mathlib-style `/-! # ... -/` blocks on all 19 `Spinor/*.lean` files)

### 5.3 Submission
- [x] Target: CPP 2027 (deadline ~Sep 2026) or ITP 2027
- [x] Secondary: *Advances in Applied Clifford Algebras* (journal, no deadline)
- [x] Tertiary: *Journal of Automated Reasoning*

---

## Dependencies (from Mathlib)

| What we need | Mathlib status | Notes |
|---|---|---|
| `CliffordAlgebra Q` | ✅ Complete | Universal property, lift, grading |
| `ExteriorAlgebra R M` | ✅ Complete | As quotient of tensor algebra |
| `spinGroup Q` | ✅ Basic | Group structure, conjugation action |
| `pinGroup Q` | ✅ Basic | Same |
| `QuadraticForm.Isotropic` | ⚠️ Partial | Mathlib gives the basic isotropic-subspace API; maximal totally isotropic / Witt-index packaging is built locally |
| `QuadraticForm.WittDecomp` | ❌ Missing | Implemented locally in `Spinor.WittDecomp` and fed into `Spinor.Presentation` |
| Interior product on ⋀V | ⚠️ Partial | `ExteriorAlgebra.ιMulti` exists; this project adds `contractionAction` on the chosen `⋀W` models |
| Clifford module structure | ❌ Missing | Built locally via the ambient `Spinor.CliffordAction` and the chosen-model `Spinor.HyperbolicAction` / `Spinor.Presentation` APIs |

---

## Non-Goals
- Spinor bundles / differential geometry (Mathlib's manifold library too immature)
- Dirac operators (requires spinor bundles)
- Computational paths (this is standard Mathlib-style formalization)
- Physics applications (pure algebra focus)
