/-
  Witt-index bookkeeping built on top of totally isotropic subspaces.

  This file implements the finite-dimensional existence of maximal totally isotropic
  subspaces and the corresponding Witt index. It also packages a linear
  decomposition `V ≃ W ⊕ W* ⊕ V₀` once a totally isotropic subspace `W` and a
  complementary subspace are chosen. The remaining future work is to upgrade this
  linear decomposition to the fully orthogonal/hyperbolic quadratic-form splitting.
-/

import Spinor.Isotropic

namespace QuadraticForm

open Classical

set_option linter.unusedSectionVars false

universe uK uV

variable {K : Type uK} [Field K]
variable {V : Type uV} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The set of dimensions realized by totally isotropic subspaces of `Q`. -/
noncomputable def isotropicFinranks (Q : QuadraticForm K V) : Finset ℕ := by
  classical
  exact
    (Finset.range (Module.finrank K V + 1)).filter fun n =>
      ∃ W : Submodule K V, Q.IsTotallyIsotropic W ∧ Module.finrank K W = n

omit [FiniteDimensional K V] in
@[simp]
theorem zero_mem_isotropicFinranks (Q : QuadraticForm K V) :
    0 ∈ Q.isotropicFinranks := by
  refine Finset.mem_filter.mpr ?_
  refine ⟨Finset.mem_range.mpr (Nat.succ_pos _), ?_⟩
  exact ⟨⊥, Q.isTotallyIsotropic_bot, by simp⟩

/-- The Witt index of `Q`, defined as the maximal dimension of a totally isotropic subspace. -/
noncomputable def wittIndex (Q : QuadraticForm K V) : ℕ :=
  (Q.isotropicFinranks).max' ⟨0, Q.zero_mem_isotropicFinranks⟩

omit [FiniteDimensional K V] in
theorem wittIndex_mem_isotropicFinranks (Q : QuadraticForm K V) :
    Q.wittIndex ∈ Q.isotropicFinranks :=
  Finset.max'_mem _ _

theorem exists_isTotallyIsotropic_finrank_eq_wittIndex (Q : QuadraticForm K V) :
    ∃ W : Submodule K V, Q.IsTotallyIsotropic W ∧ Module.finrank K W = Q.wittIndex := by
  have hmem :
      Q.wittIndex ∈
        (Finset.range (Module.finrank K V + 1)).filter fun n =>
          ∃ W : Submodule K V, Q.IsTotallyIsotropic W ∧ Module.finrank K W = n := by
    simpa [wittIndex, isotropicFinranks] using Q.wittIndex_mem_isotropicFinranks
  exact (Finset.mem_filter.mp hmem).2

theorem wittIndex_le_finrank (Q : QuadraticForm K V) :
    Q.wittIndex ≤ Module.finrank K V := by
  have hmem :
      Q.wittIndex ∈
        (Finset.range (Module.finrank K V + 1)).filter fun n =>
          ∃ W : Submodule K V, Q.IsTotallyIsotropic W ∧ Module.finrank K W = n := by
    simpa [wittIndex, isotropicFinranks] using Q.wittIndex_mem_isotropicFinranks
  exact Nat.lt_succ_iff.mp <| Finset.mem_range.mp <| (Finset.mem_filter.mp hmem).1

theorem finrank_le_wittIndex {Q : QuadraticForm K V} {W : Submodule K V}
    (hW : Q.IsTotallyIsotropic W) :
    Module.finrank K W ≤ Q.wittIndex := by
  have hW_top : W ≤ (⊤ : Submodule K V) := by
    intro x hx
    simp
  have hdim : Module.finrank K W ≤ Module.finrank K V := by
    simpa using
      (Submodule.finrank_mono hW_top :
        Module.finrank K W ≤ Module.finrank K (⊤ : Submodule K V))
  have hrange : Module.finrank K W ∈ Finset.range (Module.finrank K V + 1) := by
    exact Finset.mem_range.mpr <| Nat.lt_succ_of_le hdim
  have hmem : Module.finrank K W ∈ Q.isotropicFinranks := by
    exact Finset.mem_filter.mpr ⟨hrange, ⟨W, hW, rfl⟩⟩
  exact Finset.le_max' _ _ hmem

theorem isMaximalTotallyIsotropic_of_finrank_eq_wittIndex {Q : QuadraticForm K V}
    {W : Submodule K V} (hW : Q.IsTotallyIsotropic W)
    (hWdim : Module.finrank K W = Q.wittIndex) :
    Q.IsMaximalTotallyIsotropic W := by
  refine ⟨hW, ?_⟩
  intro U hU hWU
  refine (Submodule.eq_of_le_of_finrank_eq hWU ?_).symm
  refine Nat.le_antisymm ?_ ?_
  · exact Submodule.finrank_mono hWU
  · simpa [hWdim] using Q.finrank_le_wittIndex hU

theorem exists_maximalTotallyIsotropic (Q : QuadraticForm K V) :
    ∃ W : Submodule K V, Q.IsMaximalTotallyIsotropic W := by
  rcases Q.exists_isTotallyIsotropic_finrank_eq_wittIndex with ⟨W, hW, hWdim⟩
  exact ⟨W, Q.isMaximalTotallyIsotropic_of_finrank_eq_wittIndex hW hWdim⟩

/-- A fixed totally isotropic subspace of dimension `wittIndex`, chosen noncomputably. -/
noncomputable def wittSubspace (Q : QuadraticForm K V) : Submodule K V :=
  Classical.choose (Q.exists_isTotallyIsotropic_finrank_eq_wittIndex)

theorem wittSubspace_isTotallyIsotropic (Q : QuadraticForm K V) :
    Q.IsTotallyIsotropic Q.wittSubspace :=
  (Classical.choose_spec (Q.exists_isTotallyIsotropic_finrank_eq_wittIndex)).1

theorem finrank_wittSubspace (Q : QuadraticForm K V) :
    Module.finrank K Q.wittSubspace = Q.wittIndex :=
  (Classical.choose_spec (Q.exists_isTotallyIsotropic_finrank_eq_wittIndex)).2

theorem wittSubspace_isMaximalTotallyIsotropic (Q : QuadraticForm K V) :
    Q.IsMaximalTotallyIsotropic Q.wittSubspace := by
  refine ⟨Q.wittSubspace_isTotallyIsotropic, ?_⟩
  intro U hU hWU
  apply (Submodule.eq_of_le_of_finrank_eq hWU ?_).symm
  refine Nat.le_antisymm ?_ ?_
  · exact Submodule.finrank_mono hWU
  · simpa [Q.finrank_wittSubspace] using Q.finrank_le_wittIndex hU

section Split

variable [Invertible (2 : K)]
variable {Q : QuadraticForm K V} {W U : Submodule K V}

/-- A totally isotropic subspace is contained in its associated-bilinear orthogonal complement. -/
theorem IsTotallyIsotropic.le_associated_orthogonal (hW : Q.IsTotallyIsotropic W) :
    W ≤ LinearMap.BilinForm.orthogonal Q.associated W := by
  intro w hw n hn
  exact (QuadraticMap.associated_isOrtho (Q := Q)).2 <| hW.isOrtho ⟨n, hn⟩ ⟨w, hw⟩

/-- In split rank, a totally isotropic subspace equals its associated-bilinear orthogonal
complement. -/
theorem associated_orthogonal_eq_of_isTotallyIsotropic_split
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) :
    LinearMap.BilinForm.orthogonal Q.associated W = W := by
  refine (Submodule.eq_of_le_of_finrank_eq hW.le_associated_orthogonal ?_).symm
  change Module.finrank K W =
    Module.finrank K (LinearMap.BilinForm.orthogonal Q.associated W)
  rw [LinearMap.BilinForm.finrank_orthogonal ((Q.nondegenerate_associated_iff).2 hQ), hsplit]
  omega

/-- The associated bilinear form pairs a complement of a split isotropic half with `W*`. -/
def associatedComplementToDual (Q : QuadraticForm K V) (W U : Submodule K V) :
    U →ₗ[K] Module.Dual K W :=
  (Q.associated.domRestrict₂ W).comp U.subtype

@[simp] theorem associatedComplementToDual_apply (Q : QuadraticForm K V) (W U : Submodule K V)
    (u : U) (w : W) :
    associatedComplementToDual (K := K) Q W U u w = Q.associated u w := rfl

/-- The associated bilinear form also pairs `W` with the dual of a chosen complement `U`. -/
def associatedToComplementDual (Q : QuadraticForm K V) (W U : Submodule K V) :
    W →ₗ[K] Module.Dual K U :=
  Q.associated.domRestrict₁₂ W U

@[simp] theorem associatedToComplementDual_apply (Q : QuadraticForm K V) (W U : Submodule K V)
    (w : W) (u : U) :
    associatedToComplementDual (K := K) Q W U w u = Q.associated w u :=
  rfl

/-- For a split isotropic half `W`, the associated pairing identifies any chosen complement with
`W*`. -/
theorem associatedComplementToDual_injective
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    Function.Injective (associatedComplementToDual (K := K) Q W U) := by
  intro u v huv
  have huv0 : associatedComplementToDual (K := K) Q W U (u - v) = 0 := by
    rw [(associatedComplementToDual (K := K) Q W U).map_sub, huv, sub_self]
  have huvOrth : ((u - v : U) : V) ∈ LinearMap.BilinForm.orthogonal Q.associated W := by
    intro w hw
    have hEval0 :=
      congrArg (fun d : Module.Dual K W => d ⟨w, hw⟩) huv0
    have hEval : Q.associated ((u - v : U) : V) w = 0 := by
      simpa using hEval0
    change Q.associated w ((u - v : U) : V) = 0
    exact (QuadraticMap.associated_isSymm (S := K) (Q := Q) w ((u - v : U) : V)).trans hEval
  have huvW : ((u - v : U) : V) ∈ W := by
    rw [associated_orthogonal_eq_of_isTotallyIsotropic_split (Q := Q) hQ hW hsplit] at huvOrth
    exact huvOrth
  have huvBot : (((u - v : U) : V)) = 0 := by
    have huvMem : (((u - v : U) : V)) ∈ W ⊓ U := ⟨huvW, (u - v).property⟩
    have : (((u - v : U) : V)) ∈ (⊥ : Submodule K V) := by
      simpa [hWU.disjoint.eq_bot] using huvMem
    simpa using this
  have hsub : u - v = 0 := by
    ext
    exact huvBot
  exact sub_eq_zero.mp hsub

/-- For a split isotropic half `W`, any chosen complement is linearly equivalent to `W*` via the
associated bilinear pairing. -/
noncomputable def associatedComplementToDualEquiv
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    U ≃ₗ[K] Module.Dual K W :=
  LinearEquiv.ofInjectiveOfFinrankEq
    (associatedComplementToDual (K := K) Q W U)
    (associatedComplementToDual_injective (Q := Q) hQ hW hsplit hWU) <| by
      rw [Subspace.dual_finrank_eq]
      have hsum : Module.finrank K W + Module.finrank K U = Module.finrank K V :=
        Submodule.finrank_add_eq_of_isCompl hWU
      omega

/-- In the same split situation, the associated pairing also identifies `W` with `U*`. -/
theorem associatedToComplementDual_injective
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W) (hWU : IsCompl W U) :
    Function.Injective (associatedToComplementDual (K := K) Q W U) := by
  intro w z hwz
  have hwz0 : associatedToComplementDual (K := K) Q W U (w - z) = 0 := by
    rw [(associatedToComplementDual (K := K) Q W U).map_sub, hwz, sub_self]
  have hzero : ((w - z : W) : V) = 0 := by
    have hnondeg := (Q.nondegenerate_associated_iff).2 hQ
    exact hnondeg.1 ((w - z : W) : V) <| by
      intro x
      have hx_top : x ∈ W ⊔ U := by
        simp [hWU.sup_eq_top]
      rcases Submodule.mem_sup.mp hx_top with ⟨y, hy, u, hu, rfl⟩
      have hy0 : Q.associated ((w - z : W) : V) y = 0 := by
        exact (QuadraticMap.associated_isOrtho (Q := Q)).2 <| hW.isOrtho (w - z) ⟨y, hy⟩
      have hu0 : Q.associated ((w - z : W) : V) u = 0 := by
        have hEval0 :=
          congrArg (fun d : Module.Dual K U => d ⟨u, hu⟩) hwz0
        simpa using hEval0
      change Q.associated ((w - z : W) : V) (y + u) = 0
      have hadd :
          Q.associated ((w - z : W) : V) (y + u) =
            Q.associated ((w - z : W) : V) y + Q.associated ((w - z : W) : V) u := by
        exact (Q.associated ((w - z : W) : V)).map_add y u
      rw [hadd, hy0, hu0]
      simp
  exact Subtype.ext <| sub_eq_zero.mp <| by simpa using hzero

noncomputable def associatedToComplementDualEquiv
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    W ≃ₗ[K] Module.Dual K U :=
  LinearEquiv.ofInjectiveOfFinrankEq
    (associatedToComplementDual (K := K) Q W U)
    (associatedToComplementDual_injective (Q := Q) hQ hW hWU)
    (by
      have hsum : Module.finrank K W + Module.finrank K U = Module.finrank K V :=
        Submodule.finrank_add_eq_of_isCompl hWU
      have hU : Module.finrank K U = Module.finrank K W := by
        omega
      classical
      rw [Subspace.dual_finrank_eq, hU])

/-- For any totally isotropic `W` with a chosen complementary subspace `U`, the associated
bilinear form pairs `U` surjectively onto `W*`. -/
theorem associatedComplementToDual_surjective
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W) (hWU : IsCompl W U) :
    Function.Surjective (associatedComplementToDual (K := K) Q W U) := by
  let B : U →ₗ[K] W →ₗ[K] K := associatedComplementToDual (K := K) Q W U
  have hflipEq : B.flip = associatedToComplementDual (K := K) Q W U := by
    ext w u
    change Q.associated (u : V) w = Q.associated (w : V) u
    simpa using (QuadraticMap.associated_isSymm (S := K) (Q := Q) (u : V) (w : V))
  have hflip : Function.Injective B.flip := by
    rw [hflipEq]
    exact associatedToComplementDual_injective (Q := Q) hQ hW hWU
  exact (LinearMap.flip_injective_iff₂ (B := B)).1 hflip

/-- The residual anisotropic factor attached to a totally isotropic `W` and a chosen complement
`U`: it is the part of `U` orthogonal to `W` for the associated bilinear form. -/
def wittResidualSubspaceOfIsCompl (Q : QuadraticForm K V) (W U : Submodule K V) :
    Submodule K U :=
  LinearMap.ker (associatedComplementToDual (K := K) Q W U)

/-- The residual factor has the expected codimension inside the chosen complement. -/
theorem finrank_wittResidualSubspaceOfIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W) (hWU : IsCompl W U) :
    Module.finrank K (wittResidualSubspaceOfIsCompl (K := K) Q W U) =
      Module.finrank K V - 2 * Module.finrank K W := by
  let α := associatedComplementToDual (K := K) Q W U
  have hsurj : Function.Surjective α :=
    associatedComplementToDual_surjective (Q := Q) hQ hW hWU
  have hdimα := LinearMap.finrank_range_add_finrank_ker α
  have hsum : Module.finrank K W + Module.finrank K U = Module.finrank K V :=
    Submodule.finrank_add_eq_of_isCompl hWU
  have hdimα' : Module.finrank K (LinearMap.ker α) =
      Module.finrank K V - 2 * Module.finrank K W := by
    rw [LinearMap.range_eq_top.2 hsurj] at hdimα
    simp [Subspace.dual_finrank_eq] at hdimα
    omega
  simpa [wittResidualSubspaceOfIsCompl, α] using hdimα'

/-- A chosen complement inside `U` to the residual factor, representing the `W*`-part of the
general linear Witt decomposition. -/
noncomputable def wittDualSubspaceOfIsCompl (Q : QuadraticForm K V) (W U : Submodule K V) :
    Submodule K U :=
  Classical.choose (wittResidualSubspaceOfIsCompl (K := K) Q W U).exists_isCompl

/-- The chosen dual part inside `U` is complementary to the residual factor. -/
theorem wittDualSubspaceOfIsCompl_isCompl (Q : QuadraticForm K V) (W U : Submodule K V) :
    IsCompl (wittResidualSubspaceOfIsCompl (K := K) Q W U)
      (wittDualSubspaceOfIsCompl (K := K) Q W U) :=
  Classical.choose_spec (wittResidualSubspaceOfIsCompl (K := K) Q W U).exists_isCompl

/-- The chosen dual part inside `U` maps to `W*` via the associated bilinear pairing. -/
noncomputable def wittDualSubspaceToDual (Q : QuadraticForm K V) (W U : Submodule K V) :
    wittDualSubspaceOfIsCompl (K := K) Q W U →ₗ[K] Module.Dual K W :=
  (associatedComplementToDual (K := K) Q W U).comp
    (wittDualSubspaceOfIsCompl (K := K) Q W U).subtype

/-- The chosen dual part really injects into `W*`. -/
theorem wittDualSubspaceToDual_injective
    (Q : QuadraticForm K V) (W U : Submodule K V) :
    Function.Injective (wittDualSubspaceToDual (K := K) Q W U) := by
  let R := wittResidualSubspaceOfIsCompl (K := K) Q W U
  let C := wittDualSubspaceOfIsCompl (K := K) Q W U
  intro c d hcd
  have hcd0 : wittDualSubspaceToDual (K := K) Q W U (c - d) = 0 := by
    rw [(wittDualSubspaceToDual (K := K) Q W U).map_sub, hcd, sub_self]
  have hker : (((c - d : C) : U)) ∈ R := by
    change associatedComplementToDual (K := K) Q W U (((c - d : C) : C) : U) = 0
    simpa [wittDualSubspaceToDual]
      using hcd0
  have hzero : (((c - d : C) : U)) = 0 := by
    have hmem : (((c - d : C) : U)) ∈ R ⊓ C := ⟨hker, (c - d).property⟩
    have : (((c - d : C) : U)) ∈ (⊥ : Submodule K U) := by
      simpa [R, C, (wittDualSubspaceOfIsCompl_isCompl (K := K) Q W U).disjoint.eq_bot] using hmem
    simpa using this
  exact sub_eq_zero.mp <| Subtype.ext hzero

/-- The chosen dual part already captures all of `W*`. -/
theorem wittDualSubspaceToDual_surjective
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W) (hWU : IsCompl W U) :
    Function.Surjective (wittDualSubspaceToDual (K := K) Q W U) := by
  let α := associatedComplementToDual (K := K) Q W U
  let R := wittResidualSubspaceOfIsCompl (K := K) Q W U
  let C := wittDualSubspaceOfIsCompl (K := K) Q W U
  let eU : U ≃ₗ[K] R × C :=
    (Submodule.prodEquivOfIsCompl R C (wittDualSubspaceOfIsCompl_isCompl (K := K) Q W U)).symm
  intro φ
  obtain ⟨u, hu⟩ := associatedComplementToDual_surjective (Q := Q) hQ hW hWU φ
  let rc := eU u
  have hdecomp : (((rc.1 : R) : U) + rc.2 : U) = u := by
    change (Submodule.prodEquivOfIsCompl R C
      (wittDualSubspaceOfIsCompl_isCompl (K := K) Q W U)) rc = u
    exact (Submodule.prodEquivOfIsCompl R C
      (wittDualSubspaceOfIsCompl_isCompl (K := K) Q W U)).apply_symm_apply u
  have hker0 : α (((rc.1 : R) : U)) = 0 := rc.1.property
  have hpair : α ((((rc.1 : R) : U) + rc.2 : U)) = φ := by
    simpa [α, hdecomp] using hu
  rw [LinearMap.map_add, hker0, zero_add] at hpair
  exact ⟨rc.2, by simpa [wittDualSubspaceToDual, α, C] using hpair⟩

/-- The chosen dual part is linearly equivalent to `W*`. -/
noncomputable def wittDualSubspaceEquivDual
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W) (hWU : IsCompl W U) :
    wittDualSubspaceOfIsCompl (K := K) Q W U ≃ₗ[K] Module.Dual K W :=
  LinearEquiv.ofBijective
    (wittDualSubspaceToDual (K := K) Q W U)
    ⟨wittDualSubspaceToDual_injective (K := K) Q W U,
      wittDualSubspaceToDual_surjective (Q := Q) hQ hW hWU⟩

/-- A totally isotropic subspace `W` together with a chosen complement `U` yields a linear
decomposition `V ≃ W ⊕ W* ⊕ V₀`, where `V₀` is the residual part of `U` orthogonal to `W`. -/
noncomputable def wittLinearDecompositionOfIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W) (hWU : IsCompl W U) :
    V ≃ₗ[K] W × Module.Dual K W × wittResidualSubspaceOfIsCompl (K := K) Q W U := by
  let R := wittResidualSubspaceOfIsCompl (K := K) Q W U
  let C := wittDualSubspaceOfIsCompl (K := K) Q W U
  let eV : V ≃ₗ[K] W × U := (Submodule.prodEquivOfIsCompl W U hWU).symm
  let eU : U ≃ₗ[K] R × C :=
    (Submodule.prodEquivOfIsCompl R C (wittDualSubspaceOfIsCompl_isCompl (K := K) Q W U)).symm
  let eC : C ≃ₗ[K] Module.Dual K W :=
    wittDualSubspaceEquivDual (Q := Q) hQ hW hWU
  exact
    (eV.trans <|
      LinearEquiv.prodCongr (LinearEquiv.refl K W) eU).trans <|
        LinearEquiv.prodCongr (LinearEquiv.refl K W) <|
          (LinearEquiv.prodComm K R C).trans <|
            LinearEquiv.prodCongr eC (LinearEquiv.refl K R)

/-- The associated self-pairing on a chosen complement. -/
def associatedComplementSelf (Q : QuadraticForm K V) (U : Submodule K V) :
    U →ₗ[K] Module.Dual K U :=
  Q.associated.domRestrict₁₂ U U

@[simp] theorem associatedComplementSelf_apply (Q : QuadraticForm K V) (U : Submodule K V)
    (u u' : U) :
    associatedComplementSelf (K := K) Q U u u' = Q.associated u u' :=
  rfl

/-- The self-pairing on `U` transported back to `W` via the perfect split pairing. -/
noncomputable def complementQuadraticCorrection
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    U →ₗ[K] W :=
  (associatedToComplementDualEquiv (Q := Q) hQ hW hsplit hWU).symm.toLinearMap.comp
    (associatedComplementSelf (K := K) Q U)

@[simp] theorem complementQuadraticCorrection_spec
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U)
    (u u' : U) :
    Q.associated (complementQuadraticCorrection (Q := Q) hQ hW hsplit hWU u : V) u' =
      Q.associated u u' := by
  let e := associatedToComplementDualEquiv (Q := Q) hQ hW hsplit hWU
  have hEq :
      associatedToComplementDual (K := K) Q W U
          (complementQuadraticCorrection (Q := Q) hQ hW hsplit hWU u) =
        associatedComplementSelf (K := K) Q U u := by
    change associatedToComplementDual (K := K) Q W U (e.symm (associatedComplementSelf (K := K) Q U u)) =
      associatedComplementSelf (K := K) Q U u
    exact LinearEquiv.apply_symm_apply e (associatedComplementSelf (K := K) Q U u)
  simpa using congrArg (fun d : Module.Dual K U => d u') hEq

/-- A triangular automorphism of `W* × W` that scales the dual coordinate by `2` and shears the
`W`-coordinate by a linear correction term. -/
noncomputable def dualScaleShear (f : Module.Dual K W →ₗ[K] W) :
    (Module.Dual K W × W) ≃ₗ[K] (Module.Dual K W × W) where
  toFun p := ((2 : K) • p.1, p.2 + f p.1)
  invFun p := ((2 : K)⁻¹ • p.1, p.2 - f ((2 : K)⁻¹ • p.1))
  left_inv p := by
    ext <;> simp [sub_eq_add_neg, add_assoc, smul_smul, two_ne_zero]
  right_inv p := by
    ext <;> simp [sub_eq_add_neg, add_left_comm, add_comm, smul_smul, two_ne_zero]
  map_add' p q := by
    ext <;> simp [map_add, smul_add, add_assoc, add_left_comm, add_comm]
  map_smul' a p := by
    ext <;> simp [map_smul, smul_add, smul_smul, mul_comm, mul_assoc]

@[simp] theorem dualScaleShear_apply (f : Module.Dual K W →ₗ[K] W) (p : Module.Dual K W × W) :
    dualScaleShear (K := K) (W := W) f p = ((2 : K) • p.1, p.2 + f p.1) :=
  rfl

/-- Once a split isotropic half `W` and a complement `U` are fixed, the ambient space is linearly
equivalent to `W* × W`. This is the linear-algebra part of the split hyperbolic presentation. -/
noncomputable def splitLinearEquivOfIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    V ≃ₗ[K] Module.Dual K W × W :=
  ((Submodule.prodEquivOfIsCompl W U hWU).symm.trans <|
      LinearEquiv.prodCongr (LinearEquiv.refl K W)
        (associatedComplementToDualEquiv (Q := Q) hQ hW hsplit hWU)).trans <|
    LinearEquiv.prodComm K W (Module.Dual K W)

@[simp] theorem splitLinearEquivOfIsCompl_apply_add
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U)
    (w : W) (u : U) :
    splitLinearEquivOfIsCompl (Q := Q) hQ hW hsplit hWU ((w : V) + u) =
      (associatedComplementToDualEquiv (Q := Q) hQ hW hsplit hWU u, w) := by
  simp [splitLinearEquivOfIsCompl]

/-- The complement self-pairing, viewed as a correction term on `W*` via the split pairing
equivalence. -/
noncomputable def dualQuadraticCorrection
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    Module.Dual K W →ₗ[K] W :=
  (complementQuadraticCorrection (Q := Q) hQ hW hsplit hWU).comp
    (associatedComplementToDualEquiv (Q := Q) hQ hW hsplit hWU).symm.toLinearMap

/-- The split hyperbolic coordinates corrected so that the transported quadratic form really is
`dualProd K W`. -/
noncomputable def splitHyperbolicLinearEquivOfIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    V ≃ₗ[K] Module.Dual K W × W :=
  (splitLinearEquivOfIsCompl (Q := Q) hQ hW hsplit hWU).trans <|
    dualScaleShear (K := K) (W := W)
      ((2 : K)⁻¹ • dualQuadraticCorrection (Q := Q) hQ hW hsplit hWU)

@[simp] theorem splitHyperbolicLinearEquivOfIsCompl_apply_add
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U)
    (w : W) (u : U) :
    splitHyperbolicLinearEquivOfIsCompl (Q := Q) hQ hW hsplit hWU ((w : V) + u) =
      ((2 : K) • associatedComplementToDualEquiv (Q := Q) hQ hW hsplit hWU u,
        w + (2 : K)⁻¹ • complementQuadraticCorrection (Q := Q) hQ hW hsplit hWU u) := by
  rw [splitHyperbolicLinearEquivOfIsCompl, LinearEquiv.trans_apply,
    splitLinearEquivOfIsCompl_apply_add, dualScaleShear_apply]
  simp [dualQuadraticCorrection]

/-- A half-dimensional totally isotropic subspace together with a chosen complement yields an
explicit hyperbolic isometry `Q ≃ dualProd K W`. -/
noncomputable def splitIsometryEquivOfIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    Q.IsometryEquiv (QuadraticForm.dualProd K W) where
  toLinearEquiv := splitHyperbolicLinearEquivOfIsCompl (Q := Q) hQ hW hsplit hWU
  map_app' x := by
    let eU := associatedComplementToDualEquiv (Q := Q) hQ hW hsplit hWU
    let c := complementQuadraticCorrection (Q := Q) hQ hW hsplit hWU
    let xu := (Submodule.prodEquivOfIsCompl W U hWU).symm x
    rcases hxu : xu with ⟨w, u⟩
    have hx : x = (w : V) + u := by
      have happly := (Submodule.prodEquivOfIsCompl W U hWU).apply_symm_apply x
      change (xu.1 : V) + xu.2 = x at happly
      rw [hxu] at happly
      simpa using happly.symm
    have hw0 : Q (w : V) = 0 := hW w
    have hself : Q.associated (c u : V) u = Q u := by
      rw [complementQuadraticCorrection_spec (Q := Q) hQ hW hsplit hWU]
      simpa using (QuadraticMap.associated_eq_self_apply (S := K) (Q := Q) (u : V))
    have hself' : Q.associated u (c u : V) = Q u := by
      rw [QuadraticMap.associated_isSymm (S := K) (Q := Q) (u : V) (c u : V)]
      exact hself
    have hcross0 :
        (2 : K) * Q.associated (u : V) w = Q ((w : V) + u) - Q u := by
      have hAssoc :=
        QuadraticMap.associated_apply (S := K) (Q := Q) (u : V) (w : V)
      have hAssoc' := congrArg (fun t : K => (2 : K) * t) hAssoc
      simpa [smul_eq_mul, hw0, add_comm, add_left_comm, add_assoc, sub_eq_add_neg,
        mul_add, add_mul, mul_assoc, two_ne_zero] using hAssoc'
    have hcross : Q ((w : V) + u) = (2 : K) * Q.associated (u : V) w + Q u := by
      calc
        Q ((w : V) + u) = (Q ((w : V) + u) - Q u) + Q u := by ring
        _ = (2 : K) * Q.associated (u : V) w + Q u := by rw [hcross0]
    subst x
    change QuadraticForm.dualProd K W
        (splitHyperbolicLinearEquivOfIsCompl (Q := Q) hQ hW hsplit hWU ((w : V) + u)) =
      Q ((w : V) + u)
    rw [splitHyperbolicLinearEquivOfIsCompl_apply_add (Q := Q) hQ hW hsplit hWU]
    calc
      QuadraticForm.dualProd K W
          ((2 : K) • eU u, w + (2 : K)⁻¹ • c u)
          = ((2 : K) • eU u) (w + (2 : K)⁻¹ • c u) := rfl
      _ = (2 : K) * (eU u (w + (2 : K)⁻¹ • c u)) := by
        simp [smul_eq_mul]
      _ = (2 : K) * (eU u w + eU u ((2 : K)⁻¹ • c u)) := by
        simp
      _ = (2 : K) * Q.associated (u : V) w + Q u := by
        rw [LinearMap.map_smul]
        have hew : (eU u) w = Q.associated (u : V) w := by
          change associatedComplementToDual (K := K) Q W U u w = Q.associated (u : V) w
          simp
        have hec : (eU u) (c u) = Q.associated (u : V) (c u : V) := by
          change associatedComplementToDual (K := K) Q W U u (c u) =
            Q.associated (u : V) (c u : V)
          simp
        rw [hew, hec, hself', smul_eq_mul]
        calc
          (2 : K) * (Q.associated (u : V) w + (2 : K)⁻¹ * Q u)
              = (2 : K) * Q.associated (u : V) w + (2 : K) * ((2 : K)⁻¹ * Q u) := by ring
          _ = (2 : K) * Q.associated (u : V) w + Q u := by
            have hq2 : (2 : K) * ((2 : K)⁻¹ * Q u) = Q u := by
              calc
                (2 : K) * ((2 : K)⁻¹ * Q u) = ((2 : K) * (2 : K)⁻¹) * Q u := by ring
                _ = Q u := by simp [two_ne_zero]
            rw [hq2]
      _ = Q ((w : V) + u) := hcross.symm

@[simp] theorem splitHyperbolicLinearEquivOfIsCompl_apply_subtype
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U)
    (w : W) :
    splitHyperbolicLinearEquivOfIsCompl (Q := Q) hQ hW hsplit hWU (w : V) = (0, w) := by
  simpa using splitHyperbolicLinearEquivOfIsCompl_apply_add
    (Q := Q) hQ hW hsplit hWU w (0 : U)

@[simp] theorem splitIsometryEquivOfIsCompl_apply_subtype
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U)
    (w : W) :
    splitIsometryEquivOfIsCompl (Q := Q) hQ hW hsplit hWU (w : V) = (0, w) :=
  splitHyperbolicLinearEquivOfIsCompl_apply_subtype (Q := Q) hQ hW hsplit hWU w

@[simp] theorem splitIsometryEquivOfIsCompl_symm_inr
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U)
    (w : W) :
    (splitIsometryEquivOfIsCompl (Q := Q) hQ hW hsplit hWU).symm (0, w) = (w : V) := by
  apply (splitIsometryEquivOfIsCompl (Q := Q) hQ hW hsplit hWU).injective
  simpa using
    ((splitIsometryEquivOfIsCompl (Q := Q) hQ hW hsplit hWU).apply_symm_apply (0, w)).trans
      (splitIsometryEquivOfIsCompl_apply_subtype (Q := Q) hQ hW hsplit hWU w).symm

/-- A chosen complement of the canonical Witt subspace. -/
noncomputable def wittSubspaceComplement (Q : QuadraticForm K V) : Submodule K V :=
  Classical.choose Q.wittSubspace.exists_isCompl

/-- The chosen complement really is complementary to the canonical Witt subspace. -/
theorem wittSubspaceComplement_isCompl (Q : QuadraticForm K V) :
    IsCompl Q.wittSubspace (Q.wittSubspaceComplement) :=
  Classical.choose_spec Q.wittSubspace.exists_isCompl

/-- The residual factor attached to the canonical Witt subspace and its chosen complement. -/
noncomputable def wittResidualSubspace (Q : QuadraticForm K V) :
    Submodule K Q.wittSubspaceComplement :=
  wittResidualSubspaceOfIsCompl (K := K) Q Q.wittSubspace Q.wittSubspaceComplement

/-- The canonical residual factor has dimension `dim(V) - 2 * wittIndex`. -/
theorem finrank_wittResidualSubspace (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Module.finrank K Q.wittResidualSubspace = Module.finrank K V - 2 * Q.wittIndex := by
  simpa [wittResidualSubspace, Q.finrank_wittSubspace] using
    finrank_wittResidualSubspaceOfIsCompl (K := K) (Q := Q) (W := Q.wittSubspace)
      (U := Q.wittSubspaceComplement) hQ Q.wittSubspace_isTotallyIsotropic
      Q.wittSubspaceComplement_isCompl

/-- The canonical Witt subspace determines a linear decomposition
`V ≃ Q.wittSubspace ⊕ Q.wittSubspace* ⊕ V₀`. -/
noncomputable def wittLinearDecomposition (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    V ≃ₗ[K] Q.wittSubspace × Module.Dual K Q.wittSubspace × Q.wittResidualSubspace :=
  wittLinearDecompositionOfIsCompl (K := K) (Q := Q) (W := Q.wittSubspace)
    (U := Q.wittSubspaceComplement) hQ Q.wittSubspace_isTotallyIsotropic
    Q.wittSubspaceComplement_isCompl

/-- In split rank, the canonical residual factor vanishes. -/
theorem wittResidualSubspace_eq_bot_of_split (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    Q.wittResidualSubspace = ⊥ := by
  exact (Submodule.finrank_eq_zero).mp <| by
    have hdim := Q.finrank_wittResidualSubspace (K := K) hQ
    omega

/-- In split rank, the canonical Witt subspace determines a chosen linear splitting
`V ≃ Q.wittSubspace* × Q.wittSubspace`. -/
noncomputable def splitWittLinearEquiv (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    V ≃ₗ[K] Module.Dual K Q.wittSubspace × Q.wittSubspace := by
  have hsplit' : Module.finrank K V = 2 * Module.finrank K Q.wittSubspace := by
    simpa [Q.finrank_wittSubspace] using hsplit
  exact splitLinearEquivOfIsCompl (Q := Q) (W := Q.wittSubspace) (U := Q.wittSubspaceComplement)
    hQ Q.wittSubspace_isTotallyIsotropic hsplit' Q.wittSubspaceComplement_isCompl

/-- In split rank, the canonical Witt subspace determines corrected hyperbolic coordinates
`V ≃ Q.wittSubspace* × Q.wittSubspace`. -/
noncomputable def splitWittHyperbolicLinearEquiv (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    V ≃ₗ[K] Module.Dual K Q.wittSubspace × Q.wittSubspace := by
  have hsplit' : Module.finrank K V = 2 * Module.finrank K Q.wittSubspace := by
    simpa [Q.finrank_wittSubspace] using hsplit
  exact splitHyperbolicLinearEquivOfIsCompl
    (Q := Q) (W := Q.wittSubspace) (U := Q.wittSubspaceComplement)
    hQ Q.wittSubspace_isTotallyIsotropic hsplit' Q.wittSubspaceComplement_isCompl

/-- In split rank, the canonical Witt subspace determines an explicit hyperbolic isometry
`Q ≃ dualProd K Q.wittSubspace`. -/
noncomputable def splitWittIsometryEquiv (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace) := by
  have hsplit' : Module.finrank K V = 2 * Module.finrank K Q.wittSubspace := by
    simpa [Q.finrank_wittSubspace] using hsplit
  exact splitIsometryEquivOfIsCompl
    (Q := Q) (W := Q.wittSubspace) (U := Q.wittSubspaceComplement)
    hQ Q.wittSubspace_isTotallyIsotropic hsplit' Q.wittSubspaceComplement_isCompl

end Split

end QuadraticForm
