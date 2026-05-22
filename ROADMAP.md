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
- [x] Package the chosen-model left action of `Cl(V, Q)` on `⋀W` through the hyperbolic/Witt/split-Witt presentation APIs
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
  - presentation-free non-split action on plain `⋀W` is still a future top-level refactor
- [x] Prove this action satisfies the Clifford relation on the packaged chosen-model presentation surfaces
  - [x] In the transported hyperbolic case, prove the vector relation on `⋀W`
  - [x] Package the same vector relation on the Witt-presentation and split-Witt chosen-model APIs
  - [x] Top-level canonical split-rank capstone: `splitSpinorCliffordAction_sq_apply`
  - a presentation-free theorem-facing statement on plain `⋀W` is still future work
- [x] Prove split-model faithfulness and transport it to the hyperbolic/Witt/split-Witt chosen-model APIs
  - [x] In the split model, show `splitCliffordAction : Cl(W* × W, dualProd) → End(⋀W)` is
    surjective and injective
  - [x] Transport that faithfulness to explicit hyperbolic presentations `Q ≃ dualProd K W`,
    the Witt-presentation API, and the split-rank canonical Witt model
  - [x] Top-level canonical split-rank capstone: `splitSpinorCliffordAction_injective`
  - there is still no presentation-free top-level `⋀W` API for arbitrary non-split forms

### 2.3 The Spinor Module
- [x] **Package the ambient `SpinorModule` together with the chosen-model `⋀W` spinor-module APIs**
  - [x] The current top-level alias in `Spinor.Basic` is the ambient regular model
    `SpinorModule Q := ExteriorAlgebra R M`
  - [x] `Spinor.CliffordAction` equips that ambient model with a faithful
    `Module (CliffordAlgebra Q)` structure
  - [x] The chosen-model `⋀W` surfaces are packaged separately through
    `HyperbolicPresentation.spinorModule`, `WittExteriorModel`, and `splitSpinorModule`
  - there is still no single theorem-facing top-level alias replacing the ambient regular model by
    the chosen maximal-isotropic one
- [x] Prove split-model simplicity and transport it to the hyperbolic/Witt/split-Witt chosen-model APIs
  - [x] In the split model, prove the full Clifford module `⋀W` is simple
  - [x] Transport that simplicity to the explicit hyperbolic, Witt, and split-Witt presentation APIs
  - the fully general algebraically closed even-dimensional irreducibility theorem remains future work
- [x] Package the dimension formula in the explicit hyperbolic and canonical split settings
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
  - implemented as `Spinor.complexEvenCliffordEquivMatrix`, i.e. the standard
    `2n`-dimensional complex sum-of-squares form on `Fin n ⊕ Fin n`
- [x] Cl(n, ℂ) ≅ Mat(2^((n-1)/2), ℂ) × Mat(2^((n-1)/2), ℂ) for n odd
  - implemented as `Spinor.complexOddCliffordEquivProdMatrix`, i.e. the
    standard grouped form consisting of the even `2n` sum-of-squares block plus one extra square
- [x] Build the real-classification foundation needed for the real period-8 table
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
  - the full period-8 Bott periodicity theorem remains future work

### 4.2 Low-Dimensional Examples
- [x] Spin(2) ≃ U(1) (circle)
  - packaged as
    `Spinor.realSpin02EquivUnitaryComplex : spinGroup realCl02Form ≃* unitary ℂ`
    using Mathlib's compact negative-signature normalization
- [x] Spin(3) ≃ SU(2) (unit quaternions / Pauli matrices)
  - packaged as
    `Spinor.realSpin03EquivUnitaryQuaternion :
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
- [x] Package the ambient `SO(V,Q)`-valued spin map, its kernel, and the conditional covering theorem
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
  - [x] package the final `SO(V,Q)`-valued covering statement under that closure hypothesis via
    `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_covering_of_pairGeneratorClosure_eq_top`
  - [x] in the split hyperbolic model `dualProd K W`, package explicit pair-generator action formulas
    via `Spinor.spinSpecialOrthogonalPairGenerator_apply_dualProd`,
    `Spinor.spinSpecialOrthogonalPairGenerator_apply_dualProd_primal_transvection`, and
    `Spinor.spinSpecialOrthogonalPairGenerator_apply_dualProd_dual_transvection`
  - [x] in the split hyperbolic model `dualProd K W`, package the explicit unipotent Clifford lift of
    a hyperbolic transvection via `Spinor.dualProdTransvectionCliffordUnit`,
    `Spinor.star_coe_dualProdTransvectionCliffordUnit`,
    `Spinor.dualProdTransvectionCliffordUnit_mem_unitary`,
    `Spinor.dualProdTransvectionCliffordUnit_mem_even`, and
    `Spinor.dualProdTransvectionCliffordUnit_conjAct_eq_transvection`
  - [x] in the split hyperbolic model `dualProd K W`, package the determinant-one transport
    `GL(W) → SO(W* × W)` via `Spinor.dualProdIsometry_det_eq_one`,
    `Spinor.dualProdIsometry_mem_specialOrthogonalGroup`, and
    `Spinor.dualProdSpecialOrthogonalOfLinearEquiv`
  - [x] upgrade that transport to a faithful group embedding via
    `Spinor.dualProdSpecialOrthogonalOfLinearEquiv_apply`,
    `Spinor.dualProdSpecialOrthogonalOfLinearEquivHom`, and
    `Spinor.dualProdSpecialOrthogonalOfLinearEquiv_injective`
  - [x] package the corresponding split Levi subgroup inside `SO(W* × W)` via
    `Spinor.dualProdLeviSubgroup` and the canonical multiplicative equivalence
    `Spinor.dualProdLeviSubgroupEquivLinearEquiv : GL(W) ≃ dualProdLeviSubgroup`
  - [x] in the split hyperbolic model `dualProd K W`, package square scalings on any chosen split
     line via `Spinor.lineScalingLinearEquiv`,
     `Spinor.dualProdSpecialOrthogonalOfLinearEquiv_apply_lineScalingLinearEquiv`,
     `Spinor.spinSpecialOrthogonalPairGenerator_eq_lineScalingLinearEquiv`, and
     `Spinor.dualProdSpecialOrthogonalOf_lineScalingLinearEquiv_sq_mem_range`
  - [x] on the split exterior model `⋀W`, normalize the chosen-line square-scaling lift via
    `Spinor.splitCliffordAction_spinIotaPairOfQuadraticEqNegOne_apply_one_lineScaling` and
    `Spinor.splitCliffordAction_spinIotaPairOfQuadraticEqNegOne_eq_smul_exteriorMap_lineScaling`,
    showing the explicit torus lift acts exactly as `-(b / a)` times the exterior action of the
    corresponding line scaling
  - [x] in the split hyperbolic model `dualProd K W`, package the one-line unipotent/torus
     structure via `Spinor.dualProdTransvectionCliffordUnit_mul`,
     `Spinor.transvection_mul_transvection_eq_transvection_add`,
     `Spinor.dualProdSpecialOrthogonalOf_transvection_mul_transvection_eq_transvection_add`, and
    `Spinor.dualProdSpecialOrthogonalOf_lineScalingLinearEquiv_mul_transvection_mul_inv_eq`
  - [x] in the split hyperbolic model `dualProd K W`, package the internal Clifford-level torus
    action on the explicit transvection lifts via
    `Spinor.spinIotaPairOfQuadraticEqNegOne_conj_dualProdTransvectionCliffordUnit`
  - [x] on the chosen split exterior model `⋀W`, package the structural Levi action theorem via
    `Spinor.splitCliffordAction_eq_smul_exteriorMap_of_spinSpecialOrthogonalRepresentation_eq`
  - [x] in the split hyperbolic model `dualProd K W`, package the basis-free two-line
    determinant-one factorization of complementary line scalings into four transvections via
    `Spinor.complementaryLineScalings_eq_transvection_four` and
    `Spinor.dualProdSpecialOrthogonalOf_complementaryLineScalings_eq_transvection_four`
  - [x] package the canonical basis-diagonal `2 × 2` determinant-one blocks via
    `Spinor.basisScalingLinearEquiv`, `Spinor.basisScalingLinearEquiv_two_update_eq_transvection_four`,
    and `Spinor.dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_two_update_eq_transvection_four`
  - [x] package the global basis-dependent determinant-one diagonal factorization via
    `Spinor.basisScalingLinearEquiv_eq_noncommProd_two_update_of_prod_eq_one` and
    `Spinor.dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_eq_noncommProd_two_update_of_prod_eq_one`
  - [x] package the square-determinant basis-scaling reduction via
    `Spinor.basisScalingLinearEquiv_eq_lineScalingLinearEquiv_mul_noncommProd_two_update_of_prod_eq_sq`
    and
    `Spinor.dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_eq_lineScalingLinearEquiv_mul_noncommProd_two_update_of_prod_eq_sq`,
    splitting any basis scaling with square total determinant into one square line scaling times the
    determinant-one diagonal factorization
  - [x] package the full finite-basis square-determinant Levi factorization via
    `Spinor.linearEquiv_eq_list_basisTransvection_mul_basisScalingLinearEquiv_mul_list_basisTransvection_of_det_eq_sq`,
    `Spinor.dualProdSpecialOrthogonalOfLinearEquiv_eq_list_basisTransvection_mul_basisScalingLinearEquiv_mul_list_basisTransvection_of_det_eq_sq`,
    and
    `Spinor.dualProdSpecialOrthogonalOfLinearEquiv_eq_list_basisTransvection_mul_lineScalingLinearEquiv_mul_noncommProd_two_update_mul_list_basisTransvection_of_det_eq_sq`,
    expressing any square-determinant Levi element as basis transvections together with one
    chosen-line square scaling and the canonical determinant-one `2 \times 2` diagonal blocks
  - [x] package the corresponding finite-basis chosen-model lift via
    `Spinor.exists_list_prod_basisTransvectionCliffordUnit_eq_exteriorMap_prod`,
    `Spinor.exists_basisScalingLinearEquivCliffordUnit_eq_exteriorMap_of_prod_eq_one`,
    `Spinor.exists_basisScalingLinearEquivCliffordUnit_eq_smul_exteriorMap_of_prod_eq_sq`,
    and `Spinor.exists_linearEquivCliffordUnit_eq_smul_exteriorMap_of_det_eq_sq`,
    showing that any square-determinant Levi coordinate admits an explicit even unitary Clifford
    unit whose split action is `-(1 / u)` times the exterior action for a chosen square root `u`
  - [x] in split rank 1, formalize the square-scaling obstruction on `dualProd K K` via
    `Spinor.spinSpecialOrthogonalPairGenerator_eq_squareScaling_of_dualProd_line`,
    `Spinor.dualProdLineSquareScalingSubgroup`, and
    `Spinor.spinSpecialOrthogonalPairGeneratorSet_dualProdLine_closure_ne_top_of_exists_nonsquare_unit`
  - [x] package the exact ambient split-line spin image as
    `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_range_dualProdLine_eq_squareScalingSubgroup`,
    showing the image inside `SO(1,1)` is precisely the square-scaling subgroup
  - [x] also package the exact split-line salvage under the opposite hypothesis: if the square map on
    `Kˣ` is surjective, then
    `Spinor.spinSpecialOrthogonalPairGeneratorSet_dualProdLine_closure_eq_top_of_square_surjective`
    and
    `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_dualProdLine_of_square_surjective`
    recover surjectivity onto `SO(1,1)`, while
    `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_covering_dualProdLine_of_square_surjective`
    packages the full split-line double-cover statement
  - [x] sharpen the split-line theorem to an exact iff:
    `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_dualProdLine_iff_square_surjective`
    says the spin map onto `SO(1,1)` is surjective iff every unit is a square, and
    `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_not_surjective_dualProdLine_of_exists_nonsquare_unit`
    gives the theorem-level nonsquare obstruction; the covering version is packaged as
    `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_covering_dualProdLine_iff_square_surjective`
  - the current pair-generator closure claim is therefore **false** in split rank 1 over any field
    with a unit outside the square map, and the full spin map is not surjective there either
  - unconditional surjectivity now requires a different generator theorem or additional field
    hypotheses; the packaged covering theorem is intentionally left conditional on the closure
    hypothesis above
  - [x] strengthen square-determinant Levi sufficiency from split rank at least 3 to arbitrary
    finite basis with a distinguished line via
    `Spinor.dualProdSpecialOrthogonalOf_basisTransvectionLinearEquiv_mem_spin_range`,
    `Spinor.dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_det_eq_sq`, and
    `Spinor.dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_square_surjective`
  - [x] prove the reverse determinant-square necessity and exact finite-basis split-Levi
    spin-image iff via the top exterior pairing/star-normalization package:
    `Spinor.topExteriorPairing_splitCliffordAction_reverse_left`,
    `Spinor.splitCliffordAction_topExteriorCoeff_pairing_of_units_smul_exteriorMap`,
    `Spinor.exists_det_eq_sq_of_spinSpecialOrthogonalRepresentation_eq`, and
    `Spinor.dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_iff_exists_det_eq_sq`
  - [x] Kernel of the ambient spin-to-isometry map is `{1, -1}` in finite-dimensional
  nondegenerate rank
  - done on the ambient API by
    `Spinor.spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one`, extending the earlier
    split/hyperbolic chosen-model theorem `splitSpinorCoveringKernel_eq_one_or_neg_one`
  - further image-classification work is now outside the finite-basis Levi subgroup:
    broaden the exact criterion to larger orthogonal subgroups or spinor-norm formulations
- [x] Package ambient and split-rank non-factorization criteria for the spin representation
  - [x] in the ambient regular model, if `Q` represents `-1` and `-1 ≠ 1`, package
    `spinRepresentation_not_factor_through_isometry_of_exists_quadratic_eq_neg_one`
  - [x] in positive split rank on the ambient regular model, package
    `splitSpinRepresentation_not_factor_through_isometry`
  - [x] in positive split rank on the canonical chosen-model API via
    `splitSpinorRepresentation_not_factor_through_isometry`
  - the fully general ambient criterion remains future work and is now cleanly separated from the
    split-rank obstruction above

---

## Phase 5: Paper & Polish (Week 7-8)

### 5.1 Paper Writing
- submission-ready paper package now lives at `paper/` (`main.tex`, `refs.bib`, `README.md`) with
  venue-neutral prose tied to the exact finite-basis split-Levi theorem package; broad
  Bott-periodicity and full all-orthogonal-group image classifications are framed as separate
  projects rather than dependencies of the claimed results
- [x] Introduction: why spinors matter, why formalization is novel
- [x] Related work: lean-ga, Mathlib Clifford, what's missing
- [x] Formalization architecture
- [x] Key proof highlights (the hard parts)
- [x] Lessons learned & Mathlib gaps discovered
- [x] Future work: spinor bundles, Dirac operators

### 5.2 Code Quality
- [x] Full `lake build` clean
- [x] Zero `sorry` / `admit` sweep
- style/lint polish is complete for the submission scope: the repository has a green `lake build`, zero
  `sorry`/`admit`, Mathlib-style module documentation throughout, and a machine-checked theorem
  index imported by `Spinor.lean`
- [x] Module documentation (Mathlib-style `/-! # ... -/` blocks on all 21 `Spinor/*.lean` files)

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
