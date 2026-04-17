/-
  Exterior-algebra models attached to chosen isotropic subspaces.
-/

import Spinor.Basic
import Mathlib.Algebra.Algebra.Prod
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection

/-!
# Exterior-model spinor modules on a chosen subspace

Exterior-algebra spinor models attached to a chosen subspace `W ≤ V`, together with the
basic wedge and contraction operators and the chosen even/odd parity splitting
`⋀W = ⋀^even W ⊕ ⋀^odd W`.

When `W` is totally isotropic, wedge squares to zero on `⋀W`, giving the hyperbolic half of
the split Clifford relation; contraction against a dual vector squares to zero in all cases.
The parity submodules are classical complements exchanged by wedge and contraction. These
pieces are then consumed by `Spinor.HyperbolicAction` to transport a Clifford action along an
explicit isometry `Q ≃ dualProd K W`, and by `Spinor.Presentation` to package the resulting
chosen-model spinor data.

## Main declarations

* `ExteriorAlgebra.finrank_eq_two_pow` — `dim(⋀M) = 2 ^ dim M` for finite-dimensional `M`.
* `Spinor.finrank_spinorModule` — `dim(SpinorModule Q) = 2 ^ dim V` on the ambient exterior
  model from `Spinor.Basic`.
* `Spinor.IsotropicExteriorModel W` — the chosen exterior algebra `⋀W`.
* `Spinor.wedgeAction W`, `Spinor.contractionAction W` — exterior multiplication by `w ∈ W`
  and contraction by `d ∈ W*` on `⋀W`, together with the basic relations
  `wedgeAction_sq_apply_of_totallyIsotropic` and `contractionAction_sq_apply`.
* `Spinor.evenExteriorSubmodule W`, `Spinor.oddExteriorSubmodule W` and
  `Spinor.evenExteriorSubmodule_isCompl` — the chosen parity splitting of `⋀W` as
  complementary submodules.
* `Spinor.wedgeAction_mem_oddExteriorSubmodule`,
  `Spinor.wedgeAction_mem_evenExteriorSubmodule` — wedge flips parity; dual statements hold
  for `contractionAction`.
-/

namespace ExteriorAlgebra

open Classical

universe uK uM

variable {K : Type uK} [Field K]
variable {M : Type uM} [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- The exterior algebra of a finite-dimensional vector space has dimension `2 ^ dim M`. -/
theorem finrank_eq_two_pow :
    Module.finrank K (ExteriorAlgebra K M) = 2 ^ Module.finrank K M := by
  let I := Module.Free.ChooseBasisIndex K M
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let b : Module.Basis I K M := Module.Free.chooseBasis K M
  calc
    Module.finrank K (ExteriorAlgebra K M) = Fintype.card (Finset I) :=
      Module.finrank_eq_card_basis b.ExteriorAlgebra
    _ = 2 ^ Fintype.card I := Fintype.card_finset
    _ = 2 ^ Module.finrank K M := by rw [Module.finrank_eq_card_basis b]

end ExteriorAlgebra

namespace Spinor

open scoped DirectSum

universe uK uV

variable {K : Type uK} [Field K]
variable {V : Type uV} [AddCommGroup V] [Module K V]

section CurrentExteriorModel

variable [FiniteDimensional K V]

theorem finrank_spinorModule (Q : QuadraticForm K V) :
    Module.finrank K (SpinorModule (R := K) (M := V) Q) = 2 ^ Module.finrank K V := by
  simpa [SpinorModule] using (ExteriorAlgebra.finrank_eq_two_pow (K := K) (M := V))

end CurrentExteriorModel

section ChosenSubspaceModel

/-- The exterior algebra attached to a chosen subspace `W ≤ V`. -/
abbrev IsotropicExteriorModel (W : Submodule K V) := ExteriorAlgebra K W

/-- Exterior multiplication by a vector in the chosen subspace `W`. -/
def wedgeAction (W : Submodule K V) : W →ₗ[K] Module.End K (IsotropicExteriorModel (K := K) W) :=
  (Algebra.lmul K (ExteriorAlgebra K W)).toLinearMap.comp (ExteriorAlgebra.ι K)

theorem wedgeAction_apply (W : Submodule K V) (w : W) (x : IsotropicExteriorModel (K := K) W) :
    wedgeAction (K := K) W w x = ExteriorAlgebra.ι K w * x := by
  rfl

theorem wedgeAction_sq_apply (W : Submodule K V) (w : W) (x : IsotropicExteriorModel (K := K) W) :
    wedgeAction (K := K) W w (wedgeAction (K := K) W w x) = 0 := by
  rw [wedgeAction_apply, wedgeAction_apply, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

theorem wedgeAction_sq_apply_of_totallyIsotropic {Q : QuadraticForm K V} {W : Submodule K V}
    (hW : Q.IsTotallyIsotropic W) (w : W) (x : IsotropicExteriorModel (K := K) W) :
    wedgeAction (K := K) W w (wedgeAction (K := K) W w x) = Q w • x := by
  rw [wedgeAction_sq_apply]
  simp [hW w]

/-- The graded direct-sum decomposition of `⋀W`. -/
abbrev gradedExteriorModel (W : Submodule K V) := DirectSum ℕ (fun i => ↥(⋀[K]^i W))

/-- The canonical grading equivalence `⋀W ≃ ⨁ n, ⋀^n W`. -/
noncomputable abbrev exteriorDecompose (W : Submodule K V) :
    IsotropicExteriorModel (K := K) W ≃ₐ[K] gradedExteriorModel (K := K) W :=
  DirectSum.decomposeAlgEquiv (fun i : ℕ => ⋀[K]^i W)

/-- The even-degree part of the graded exterior direct sum. -/
def evenGradedSubmodule (W : Submodule K V) : Submodule K (gradedExteriorModel (K := K) W) where
  carrier := {x | ∀ n, ¬ Even n → x n = 0}
  zero_mem' := by
    intro n hn
    rfl
  add_mem' := by
    intro x y hx hy n hn
    simp [hx n hn, hy n hn]
  smul_mem' := by
    intro a x hx n hn
    show a • x n = 0
    rw [hx n hn, smul_zero]

/-- The odd-degree part of the graded exterior direct sum. -/
def oddGradedSubmodule (W : Submodule K V) : Submodule K (gradedExteriorModel (K := K) W) where
  carrier := {x | ∀ n, Even n → x n = 0}
  zero_mem' := by
    intro n hn
    rfl
  add_mem' := by
    intro x y hx hy n hn
    simp [hx n hn, hy n hn]
  smul_mem' := by
    intro a x hx n hn
    show a • x n = 0
    rw [hx n hn, smul_zero]

/-- The explicit even-degree summand `⋀^even W ⊆ ⋀W`. -/
noncomputable def evenExteriorSubmodule (W : Submodule K V) :
    Submodule K (IsotropicExteriorModel (K := K) W) :=
  Submodule.comap (exteriorDecompose (K := K) W).toLinearMap (evenGradedSubmodule (K := K) W)

/-- The explicit odd-degree summand `⋀^odd W ⊆ ⋀W`. -/
noncomputable def oddExteriorSubmodule (W : Submodule K V) :
    Submodule K (IsotropicExteriorModel (K := K) W) :=
  Submodule.comap (exteriorDecompose (K := K) W).toLinearMap (oddGradedSubmodule (K := K) W)

@[simp]
theorem mem_evenExteriorSubmodule_iff (W : Submodule K V) {x : IsotropicExteriorModel (K := K) W} :
    x ∈ evenExteriorSubmodule (K := K) W ↔
      ∀ n, ¬ Even n → exteriorDecompose (K := K) W x n = 0 := by
  rfl

@[simp]
theorem mem_oddExteriorSubmodule_iff (W : Submodule K V) {x : IsotropicExteriorModel (K := K) W} :
    x ∈ oddExteriorSubmodule (K := K) W ↔
      ∀ n, Even n → exteriorDecompose (K := K) W x n = 0 := by
  rfl

private theorem evenProjection_mem (W : Submodule K V) (x : gradedExteriorModel (K := K) W) :
    DFinsupp.filterLinearMap K (fun i : ℕ => ↥(⋀[K]^i W)) (fun n : ℕ => Even n) x ∈
      evenGradedSubmodule (K := K) W := by
  intro n hn
  simp [hn]

private theorem evenProjection_apply_of_mem (W : Submodule K V)
    {x : gradedExteriorModel (K := K) W} (hx : x ∈ evenGradedSubmodule (K := K) W) :
    DFinsupp.filterLinearMap K (fun i : ℕ => ↥(⋀[K]^i W)) (fun n : ℕ => Even n) x = x := by
  ext n
  by_cases h : Even n
  · simp [h]
  · simp [h, hx n h]

private theorem evenProjection_ker_eq_odd (W : Submodule K V) :
    LinearMap.ker
        (DFinsupp.filterLinearMap K (fun i : ℕ => ↥(⋀[K]^i W)) (fun n : ℕ => Even n)) =
      oddGradedSubmodule (K := K) W := by
  ext x
  constructor
  · intro hx n hn
    have hx' :
        DFinsupp.filterLinearMap K (fun i : ℕ => ↥(⋀[K]^i W)) (fun n : ℕ => Even n) x = 0 :=
      LinearMap.mem_ker.mp hx
    have hcomp := congrArg (fun y => (y n : ⋀[K]^n W)) hx'
    simpa [hn] using hcomp
  · intro hx
    ext n
    by_cases h : Even n
    · simp [h, hx n h]
    · simp [h]

theorem evenGradedSubmodule_isCompl (W : Submodule K V) :
    IsCompl (evenGradedSubmodule (K := K) W) (oddGradedSubmodule (K := K) W) := by
  have hproj : LinearMap.IsProj (evenGradedSubmodule (K := K) W)
      (DFinsupp.filterLinearMap K (fun i : ℕ => ↥(⋀[K]^i W)) (fun n : ℕ => Even n)) := by
    refine ⟨evenProjection_mem (K := K) (W := W), ?_⟩
    intro x hx
    exact evenProjection_apply_of_mem (K := K) (W := W) hx
  rw [← evenProjection_ker_eq_odd (K := K) (W := W)]
  exact hproj.isCompl

theorem evenExteriorSubmodule_eq_map (W : Submodule K V) :
    evenExteriorSubmodule (K := K) W =
      (evenGradedSubmodule (K := K) W).map (exteriorDecompose (K := K) W).symm.toLinearMap := by
  simpa using Submodule.comap_equiv_eq_map_symm (exteriorDecompose (K := K) W).toLinearEquiv
    (evenGradedSubmodule (K := K) W)

theorem oddExteriorSubmodule_eq_map (W : Submodule K V) :
    oddExteriorSubmodule (K := K) W =
      (oddGradedSubmodule (K := K) W).map (exteriorDecompose (K := K) W).symm.toLinearMap := by
  simpa using Submodule.comap_equiv_eq_map_symm (exteriorDecompose (K := K) W).toLinearEquiv
    (oddGradedSubmodule (K := K) W)

/-- The chosen-model parity splitting `⋀W = ⋀^even W ⊕ ⋀^odd W`. -/
theorem evenExteriorSubmodule_isCompl (W : Submodule K V) :
    IsCompl (evenExteriorSubmodule (K := K) W) (oddExteriorSubmodule (K := K) W) := by
  let e := Submodule.orderIsoMapComap (exteriorDecompose (K := K) W).symm.toLinearEquiv
  have h : IsCompl (e (evenGradedSubmodule (K := K) W)) (e (oddGradedSubmodule (K := K) W)) :=
    (OrderIso.isCompl_iff e
      (x := evenGradedSubmodule (K := K) W) (y := oddGradedSubmodule (K := K) W)).1
      (evenGradedSubmodule_isCompl (K := K) (W := W))
  simpa [e, evenExteriorSubmodule_eq_map, oddExteriorSubmodule_eq_map] using h

theorem evenExteriorSubmodule_sup_oddExteriorSubmodule (W : Submodule K V) :
    evenExteriorSubmodule (K := K) W ⊔ oddExteriorSubmodule (K := K) W = ⊤ :=
  (evenExteriorSubmodule_isCompl (K := K) (W := W)).sup_eq_top

theorem evenExteriorSubmodule_inf_oddExteriorSubmodule (W : Submodule K V) :
    evenExteriorSubmodule (K := K) W ⊓ oddExteriorSubmodule (K := K) W = ⊥ :=
  (evenExteriorSubmodule_isCompl (K := K) (W := W)).inf_eq_bot

private theorem gradeOne_mul_mem_oddGradedSubmodule (W : Submodule K V) (a : ↥(⋀[K]^1 W))
    {x : gradedExteriorModel (K := K) W} (hx : x ∈ evenGradedSubmodule (K := K) W) :
    DirectSum.of (fun i : ℕ => ↥(⋀[K]^i W)) 1 a * x ∈ oddGradedSubmodule (K := K) W := by
  intro n hn
  apply Subtype.ext
  by_cases h : 1 ≤ n
  · have hnot : ¬ Even (n - 1) := by
      have hodd : Odd (n - 1) := by
        rw [Nat.odd_sub' h]
        simp [hn]
      exact Nat.not_even_iff_odd.mpr hodd
    rw [show ↑(((DirectSum.of (fun i : ℕ => ↥(⋀[K]^i W)) 1) a * x) n) =
          (a : ExteriorAlgebra K W) * ↑(x (n - 1)) by
          simpa using (DirectSum.coe_of_mul_apply_of_le (A := fun i : ℕ => ⋀[K]^i W) a x n h)]
    simp [hx (n - 1) hnot]
  · simpa using (DirectSum.coe_of_mul_apply_of_not_le (A := fun i : ℕ => ⋀[K]^i W) a x n h)

private theorem gradeOne_mul_mem_evenGradedSubmodule (W : Submodule K V) (a : ↥(⋀[K]^1 W))
    {x : gradedExteriorModel (K := K) W} (hx : x ∈ oddGradedSubmodule (K := K) W) :
    DirectSum.of (fun i : ℕ => ↥(⋀[K]^i W)) 1 a * x ∈ evenGradedSubmodule (K := K) W := by
  intro n hn
  apply Subtype.ext
  by_cases h : 1 ≤ n
  · have heven : Even (n - 1) := by
      have hsimp : Even (n - 1) ↔ ¬ Even n := by
        simpa using (Nat.even_sub h : Even (n - 1) ↔ (Even n ↔ Even 1))
      exact hsimp.mpr hn
    rw [show ↑(((DirectSum.of (fun i : ℕ => ↥(⋀[K]^i W)) 1) a * x) n) =
          (a : ExteriorAlgebra K W) * ↑(x (n - 1)) by
          simpa using (DirectSum.coe_of_mul_apply_of_le (A := fun i : ℕ => ⋀[K]^i W) a x n h)]
    simp [hx (n - 1) heven]
  · simpa using (DirectSum.coe_of_mul_apply_of_not_le (A := fun i : ℕ => ⋀[K]^i W) a x n h)

@[simp]
theorem exteriorDecompose_ι (W : Submodule K V) (w : W) :
    exteriorDecompose (K := K) W ((ExteriorAlgebra.ι K) w) =
      DirectSum.of (fun i : ℕ => ↥(⋀[K]^i W)) 1
        ⟨(ExteriorAlgebra.ι K) w, by
          simpa only [pow_one] using LinearMap.mem_range_self (ExteriorAlgebra.ι K) w⟩ := by
  simpa [exteriorDecompose] using
    (ExteriorAlgebra.GradedAlgebra.liftι_eq (R := K) (M := W) 1
      ⟨(ExteriorAlgebra.ι K) w, by
        simpa only [pow_one] using LinearMap.mem_range_self (ExteriorAlgebra.ι K) w⟩)

theorem exteriorDecompose_wedge (W : Submodule K V) (w : W) (x : IsotropicExteriorModel (K := K) W) :
    exteriorDecompose (K := K) W (wedgeAction (K := K) W w x) =
      DirectSum.of (fun i : ℕ => ↥(⋀[K]^i W)) 1
          ⟨(ExteriorAlgebra.ι K) w, by
            simpa only [pow_one] using LinearMap.mem_range_self (ExteriorAlgebra.ι K) w⟩ *
        exteriorDecompose (K := K) W x := by
  rw [wedgeAction_apply, map_mul, exteriorDecompose_ι]

/-- Exterior multiplication by a vector flips the chosen even/odd splitting. -/
theorem wedgeAction_mem_oddExteriorSubmodule (W : Submodule K V) (w : W)
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ evenExteriorSubmodule (K := K) W) :
    wedgeAction (K := K) W w x ∈ oddExteriorSubmodule (K := K) W := by
  change exteriorDecompose (K := K) W (wedgeAction (K := K) W w x) ∈ oddGradedSubmodule (K := K) W
  change exteriorDecompose (K := K) W x ∈ evenGradedSubmodule (K := K) W at hx
  rw [exteriorDecompose_wedge]
  exact gradeOne_mul_mem_oddGradedSubmodule (K := K) (W := W) _ hx

/-- Exterior multiplication by a vector flips the chosen odd/even splitting. -/
theorem wedgeAction_mem_evenExteriorSubmodule (W : Submodule K V) (w : W)
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ oddExteriorSubmodule (K := K) W) :
    wedgeAction (K := K) W w x ∈ evenExteriorSubmodule (K := K) W := by
  change exteriorDecompose (K := K) W (wedgeAction (K := K) W w x) ∈ evenGradedSubmodule (K := K) W
  change exteriorDecompose (K := K) W x ∈ oddGradedSubmodule (K := K) W at hx
  rw [exteriorDecompose_wedge]
  exact gradeOne_mul_mem_evenGradedSubmodule (K := K) (W := W) _ hx

section Contraction

variable [Invertible (2 : K)]

/--
Interior multiplication by a covector on the chosen subspace `W`, obtained by transporting
`CliffordAlgebra.contractLeft` along the equivalence between the zero-form Clifford algebra and the
exterior algebra.
-/
def contractionAction (W : Submodule K V) :
    Module.Dual K W →ₗ[K] Module.End K (IsotropicExteriorModel (K := K) W) :=
  (LinearEquiv.conj (CliffordAlgebra.equivExterior (0 : QuadraticForm K W))).toLinearMap.comp
    (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K W)))

theorem contractionAction_apply (W : Submodule K V) (d : Module.Dual K W)
    (x : IsotropicExteriorModel (K := K) W) :
    contractionAction (K := K) W d x =
      CliffordAlgebra.equivExterior (0 : QuadraticForm K W)
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K W)) d
          ((CliffordAlgebra.equivExterior (0 : QuadraticForm K W)).symm x)) := by
  rfl

theorem contractionAction_symm_apply (W : Submodule K V) (d : Module.Dual K W)
    (x : IsotropicExteriorModel (K := K) W) :
    (CliffordAlgebra.equivExterior (0 : QuadraticForm K W)).symm
        (contractionAction (K := K) W d x) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K W)) d
        ((CliffordAlgebra.equivExterior (0 : QuadraticForm K W)).symm x) := by
  rw [contractionAction_apply]
  exact (CliffordAlgebra.equivExterior (0 : QuadraticForm K W)).left_inv _

theorem contractionAction_ι (W : Submodule K V) (d : Module.Dual K W) (w : W) :
    contractionAction (K := K) W d (ExteriorAlgebra.ι K w) = algebraMap K _ (d w) := by
  rw [contractionAction_apply]
  simp

theorem contractionAction_sq_apply (W : Submodule K V) (d : Module.Dual K W)
    (x : IsotropicExteriorModel (K := K) W) :
    contractionAction (K := K) W d (contractionAction (K := K) W d x) = 0 := by
  apply (CliffordAlgebra.equivExterior (0 : QuadraticForm K W)).symm.injective
  rw [map_zero, contractionAction_symm_apply, contractionAction_symm_apply]
  exact CliffordAlgebra.contractLeft_contractLeft d _

theorem symm_wedge_mul (W : Submodule K V) (w : W) (x : IsotropicExteriorModel (K := K) W) :
    (CliffordAlgebra.equivExterior (0 : QuadraticForm K W)).symm ((ExteriorAlgebra.ι K) w * x) =
      CliffordAlgebra.ι (0 : QuadraticForm K W) w *
        (CliffordAlgebra.equivExterior (0 : QuadraticForm K W)).symm x := by
  simp [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv, CliffordAlgebra.changeForm_ι_mul]

theorem contractionAction_ι_mul (W : Submodule K V) (d : Module.Dual K W) (w : W)
    (x : IsotropicExteriorModel (K := K) W) :
    contractionAction (K := K) W d ((ExteriorAlgebra.ι K) w * x) =
      d w • x - (ExteriorAlgebra.ι K) w * contractionAction (K := K) W d x := by
  apply (CliffordAlgebra.equivExterior (0 : QuadraticForm K W)).symm.injective
  rw [map_sub, map_smul, contractionAction_symm_apply, symm_wedge_mul, symm_wedge_mul,
    contractionAction_symm_apply]
  simp [CliffordAlgebra.contractLeft_ι_mul]

theorem contractionAction_algebraMap (W : Submodule K V) (d : Module.Dual K W) (r : K) :
    contractionAction (K := K) W d (algebraMap K (IsotropicExteriorModel (K := K) W) r) = 0 := by
  apply (CliffordAlgebra.equivExterior (0 : QuadraticForm K W)).symm.injective
  rw [map_zero, contractionAction_symm_apply]
  simp

section BasisActions

variable {I : Type*} [LinearOrder I]
variable {W : Submodule K V}

omit [Invertible (2 : K)] in
theorem basis_empty (b : Module.Basis I K W) :
    b.ExteriorAlgebra (∅ : Finset I) = 1 := by
  rw [ExteriorAlgebra.basis_apply_ofCard (R := K) (n := 0) (b := b) (s := (∅ : Finset I))
      (by simp)]
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_zero_apply]

omit [Invertible (2 : K)] in
theorem basis_singleton (b : Module.Basis I K W) (i : I) :
    b.ExteriorAlgebra ({i} : Finset I) = ExteriorAlgebra.ι K (b i) := by
  rw [ExteriorAlgebra.basis_apply_ofCard (R := K) (n := 1) (b := b) (s := ({i} : Finset I))
      (by simp)]
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, Finset.orderEmbOfFin_singleton]

omit [Invertible (2 : K)] in
private theorem basis_eq_unit_smul_wedge_basis_erase
    (b : Module.Basis I K W) {i : I} {s : Finset I} (hi : i ∈ s) :
    ∃ c : K, c * c = 1 ∧
      b.ExteriorAlgebra s =
        c • ((ExteriorAlgebra.ι K (b i)) * b.ExteriorAlgebra (s.erase i)) := by
  let s₁ : Set.powersetCard I 1 := ⟨{i}, by simp⟩
  let t : Set.powersetCard I (s.erase i).card := ⟨s.erase i, rfl⟩
  have hdis : Disjoint s₁.val t.val := by
    simp [s₁, t]
  have hmul :
      b.ExteriorAlgebra ({i} : Finset I) * b.ExteriorAlgebra (s.erase i) =
        (((Set.powersetCard.permOfDisjoint hdis).sign : K)) •
          b.ExteriorAlgebra (insert i (s.erase i)) := by
    simpa [s₁, t, basis_singleton] using
      (ExteriorAlgebra.basis_mul_of_disjoint (R := K) (b := b) (s := s₁) (t := t) hdis)
  let c : K := ((Set.powersetCard.permOfDisjoint hdis).sign : K)
  have hc : c * c = 1 := by
    dsimp [c]
    rw [← Int.cast_mul]
    simp
  refine ⟨c, hc, ?_⟩
  calc
    b.ExteriorAlgebra s
        = b.ExteriorAlgebra (insert i (s.erase i)) := by simp [hi]
    _ = c •
          (c •
          b.ExteriorAlgebra (insert i (s.erase i))) := by
            simp [c, smul_smul, hc]
    _ = c •
          ((ExteriorAlgebra.ι K (b i)) * b.ExteriorAlgebra (s.erase i)) := by
          simpa [c, basis_singleton] using congrArg (fun x => c • x) (Eq.symm hmul)

omit [Invertible (2 : K)] in
theorem wedgeAction_basis_eq_zero_of_mem
    (b : Module.Basis I K W) {i : I} {s : Finset I} (hi : i ∈ s) :
    wedgeAction (K := K) W (b i) (b.ExteriorAlgebra s) = 0 := by
  rw [wedgeAction_apply]
  let s₁ : Set.powersetCard I 1 := ⟨{i}, by simp⟩
  let t : Set.powersetCard I s.card := ⟨s, rfl⟩
  have hnot : ¬ Disjoint s₁.val t.val := by
    simp [s₁, t, hi]
  simpa [s₁, t, basis_singleton] using
    (ExteriorAlgebra.basis_mul_of_not_disjoint (R := K) (b := b) (s := s₁) (t := t) hnot)

theorem contractionAction_basis_eq_zero_of_not_mem
    (b : Module.Basis I K W) (i : I) :
    ∀ {s : Finset I}, i ∉ s →
      contractionAction (K := K) W (b.coord i) (b.ExteriorAlgebra s) = 0
  := by
  intro s hs
  induction s using Finset.induction_on with
  | empty =>
      simpa [basis_empty] using
        contractionAction_algebraMap (K := K) (W := W) (d := b.coord i) (r := 1)
  | @insert j s hj ih =>
      have hji : i ≠ j := by
        intro h
        exact hs (h ▸ Finset.mem_insert_self _ _)
      have his : i ∉ s := by
        simpa [Finset.mem_insert, hji] using hs
      rcases basis_eq_unit_smul_wedge_basis_erase (K := K) (W := W) (b := b)
          (i := j) (s := insert j s) (by simp) with ⟨c, hc, hu⟩
      rw [hu, map_smul, contractionAction_ι_mul]
      have hcoord : b.coord i (b j) = 0 := by
        simp [hji]
      have hmulzero :
          (ExteriorAlgebra.ι K (b j)) *
              contractionAction (K := K) W (b.coord i) (b.ExteriorAlgebra (s.erase j)) = 0 := by
        simpa [hj] using
          congrArg (fun x => (ExteriorAlgebra.ι K (b j)) * x) (ih his)
      simp [hcoord, hmulzero]

theorem contract_wedge_basis_eq_self_of_not_mem
    (b : Module.Basis I K W) {i : I} {s : Finset I} (hi : i ∉ s) :
    contractionAction (K := K) W (b.coord i)
        (wedgeAction (K := K) W (b i) (b.ExteriorAlgebra s)) =
      b.ExteriorAlgebra s := by
  rw [wedgeAction_apply, contractionAction_ι_mul]
  have hcoord : b.coord i (b i) = 1 := by
    simp
  simp [hcoord, contractionAction_basis_eq_zero_of_not_mem (K := K) (W := W) b i hi]

theorem contract_wedge_basis_eq_zero_of_mem
    (b : Module.Basis I K W) {i : I} {s : Finset I} (hi : i ∈ s) :
    contractionAction (K := K) W (b.coord i)
        (wedgeAction (K := K) W (b i) (b.ExteriorAlgebra s)) =
      0 := by
  simp [wedgeAction_basis_eq_zero_of_mem (K := K) (W := W) b hi]

theorem wedge_contract_basis_eq_self_of_mem
    (b : Module.Basis I K W) {i : I} {s : Finset I} (hi : i ∈ s) :
    wedgeAction (K := K) W (b i)
        (contractionAction (K := K) W (b.coord i) (b.ExteriorAlgebra s)) =
      b.ExteriorAlgebra s := by
  rcases basis_eq_unit_smul_wedge_basis_erase (K := K) (W := W) (b := b) hi with ⟨c, hc, hu⟩
  rw [hu, map_smul, contractionAction_ι_mul, wedgeAction_apply]
  have hzero :
      contractionAction (K := K) W (b.coord i) (b.ExteriorAlgebra (s.erase i)) = 0 := by
    apply contractionAction_basis_eq_zero_of_not_mem (K := K) (W := W) b i
    simp
  simp [hzero]

theorem wedge_contract_basis_eq_zero_of_not_mem
    (b : Module.Basis I K W) {i : I} {s : Finset I} (hi : i ∉ s) :
    wedgeAction (K := K) W (b i)
        (contractionAction (K := K) W (b.coord i) (b.ExteriorAlgebra s)) =
      0 := by
  simp [contractionAction_basis_eq_zero_of_not_mem (K := K) (W := W) b i hi]

noncomputable def basisMembershipProjectorOp (b : Module.Basis I K W) (s : Finset I) (i : I) :
    Module.End K (IsotropicExteriorModel (K := K) W) :=
  if i ∈ s then
    (wedgeAction (K := K) W (b i)).comp (contractionAction (K := K) W (b.coord i))
  else
    (contractionAction (K := K) W (b.coord i)).comp (wedgeAction (K := K) W (b i))

theorem basisMembershipProjectorOp_apply_basis
    (b : Module.Basis I K W) (s t : Finset I) (i : I) :
    basisMembershipProjectorOp (K := K) (W := W) b s i (b.ExteriorAlgebra t) =
      if i ∈ s ↔ i ∈ t then b.ExteriorAlgebra t else 0 := by
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t
  · simp [basisMembershipProjectorOp, his, hit,
      wedge_contract_basis_eq_self_of_mem (K := K) (W := W) b hit]
  · simp [basisMembershipProjectorOp, his, hit,
      wedge_contract_basis_eq_zero_of_not_mem (K := K) (W := W) b hit]
  · simp [basisMembershipProjectorOp, his, hit,
      contract_wedge_basis_eq_zero_of_mem (K := K) (W := W) b hit]
  · simp [basisMembershipProjectorOp, his, hit,
      contract_wedge_basis_eq_self_of_not_mem (K := K) (W := W) b hit]

noncomputable def basisMembershipProjectorAux (b : Module.Basis I K W) (s : Finset I) :
    List I → Module.End K (IsotropicExteriorModel (K := K) W)
  | [] => LinearMap.id
  | i :: l =>
      (basisMembershipProjectorAux b s l).comp (basisMembershipProjectorOp (K := K) (W := W) b s i)

theorem basisMembershipProjectorAux_apply_basis
    (b : Module.Basis I K W) (s t : Finset I) :
    ∀ l,
      basisMembershipProjectorAux (K := K) (W := W) b s l (b.ExteriorAlgebra t) =
        if ∀ i, i ∈ l → (i ∈ s ↔ i ∈ t) then b.ExteriorAlgebra t else 0
  | [] => by
      simp [basisMembershipProjectorAux]
  | i :: l => by
      by_cases h : i ∈ s ↔ i ∈ t
      · simp [basisMembershipProjectorAux, basisMembershipProjectorOp_apply_basis,
          basisMembershipProjectorAux_apply_basis, h]
      · simp [basisMembershipProjectorAux, basisMembershipProjectorOp_apply_basis,
          h]

noncomputable def basisMembershipProjector [Fintype I] (b : Module.Basis I K W) (s : Finset I) :
    Module.End K (IsotropicExteriorModel (K := K) W) :=
  basisMembershipProjectorAux (K := K) (W := W) b s ((Finset.univ : Finset I).sort (· ≤ ·))

theorem basisMembershipProjector_apply_basis [Fintype I]
    (b : Module.Basis I K W) (s t : Finset I) :
    basisMembershipProjector (K := K) (W := W) b s (b.ExteriorAlgebra t) =
      if t = s then b.ExteriorAlgebra s else 0 := by
  rw [basisMembershipProjector, basisMembershipProjectorAux_apply_basis]
  by_cases hts : t = s
  · subst hts
    simp
  · have hcond : ¬ ∀ i, i ∈ ((Finset.univ : Finset I).sort (· ≤ ·)) → (i ∈ s ↔ i ∈ t) := by
      intro hall
      apply hts
      apply Finset.ext
      intro i
      exact (hall i (by simp)).symm
    have hcond' : ¬ ∀ i, i ∈ s ↔ i ∈ t := by
      intro hall
      exact hcond (fun i hi => hall i)
    simp [hcond', hts]

end BasisActions

private theorem contractionAction_mem_exteriorPower_pred_and_zero
    (W : Submodule K V) (d : Module.Dual K W)
    {m : ℕ} {y : ExteriorAlgebra K ↥W}
    (hy : y ∈ LinearMap.range (ExteriorAlgebra.ι (R := K) (M := W)) ^ m) :
    contractionAction (K := K) W d y ∈ ⋀[K]^(m - 1) W ∧
      (m = 0 → contractionAction (K := K) W d y = 0) := by
  induction hy using Submodule.pow_induction_on_left' with
  | algebraMap r =>
      refine ⟨?_, ?_⟩
      · simp [pow_zero, contractionAction_algebraMap]
      · intro hm
        simpa [hm] using contractionAction_algebraMap (K := K) (W := W) d r
  | add x y i hx hy ihx ihy =>
      refine ⟨?_, ?_⟩
      · simpa [map_add] using Submodule.add_mem (⋀[K]^(i - 1) W) ihx.1 ihy.1
      · intro hi
        rw [map_add, ihx.2 hi, ihy.2 hi, add_zero]
  | mem_mul m hm i x hx ih =>
      obtain ⟨w, rfl⟩ := hm
      refine ⟨?_, ?_⟩
      · rw [contractionAction_ι_mul]
        cases i with
        | zero =>
            rw [ih.2 rfl, mul_zero, sub_zero]
            have hx0 : x ∈ ⋀[K]^0 W := by
              simpa using hx
            exact Submodule.smul_mem _ (d w) hx0
        | succ k =>
            have hmul : (ExteriorAlgebra.ι K w) * contractionAction (K := K) W d x ∈ ⋀[K]^(k + 1) W := by
              simpa [pow_succ'] using
                (Submodule.mul_mem_mul (LinearMap.mem_range_self (ExteriorAlgebra.ι K) w) ih.1)
            exact Submodule.sub_mem _ (Submodule.smul_mem _ (d w) hx) hmul
      · intro hi
        omega

theorem contractionAction_mem_exteriorPower_pred (W : Submodule K V) (d : Module.Dual K W)
    {n : ℕ} (x : ↥(⋀[K]^n W)) :
    contractionAction (K := K) W d x ∈ ⋀[K]^(n - 1) W :=
  (contractionAction_mem_exteriorPower_pred_and_zero (K := K) W d x.2).1

theorem contractionAction_eq_zero_of_mem_exteriorPower_zero (W : Submodule K V) (d : Module.Dual K W)
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ ⋀[K]^0 W) :
    contractionAction (K := K) W d x = 0 :=
  (contractionAction_mem_exteriorPower_pred_and_zero (K := K) W d hx).2 rfl

omit [Invertible (2 : K)] in
theorem mem_oddExteriorSubmodule_of_mem_exteriorPower (W : Submodule K V)
    {n : ℕ} {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ ⋀[K]^n W) (hn : ¬ Even n) :
    x ∈ oddExteriorSubmodule (K := K) W := by
  intro m hm
  have hnm : n ≠ m := by
    intro hnm
    subst hnm
    exact hn hm
  simpa [exteriorDecompose] using
    (DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[K]^i W) hx hnm)

omit [Invertible (2 : K)] in
theorem mem_evenExteriorSubmodule_of_mem_exteriorPower (W : Submodule K V)
    {n : ℕ} {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ ⋀[K]^n W) (hn : Even n) :
    x ∈ evenExteriorSubmodule (K := K) W := by
  intro m hm
  have hnm : n ≠ m := by
    intro hnm
    subst hnm
    exact hm hn
  simpa [exteriorDecompose] using
    (DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[K]^i W) hx hnm)

theorem contractionAction_mem_oddExteriorSubmodule_of_even_degree (W : Submodule K V)
    (d : Module.Dual K W) {n : ℕ} (x : ↥(⋀[K]^n W)) (hn : Even n) :
    contractionAction (K := K) W d x ∈ oddExteriorSubmodule (K := K) W := by
  cases n with
  | zero =>
      rw [contractionAction_eq_zero_of_mem_exteriorPower_zero (K := K) (W := W) d x.2]
      exact Submodule.zero_mem _
  | succ k =>
      have hodd : ¬ Even k := by
        simpa [Nat.even_add_one] using hn
      exact mem_oddExteriorSubmodule_of_mem_exteriorPower (K := K) (W := W)
        (contractionAction_mem_exteriorPower_pred (K := K) (W := W) d x) hodd

  theorem contractionAction_mem_evenExteriorSubmodule_of_odd_degree (W : Submodule K V)
    (d : Module.Dual K W) {n : ℕ} (x : ↥(⋀[K]^n W)) (hn : ¬ Even n) :
    contractionAction (K := K) W d x ∈ evenExteriorSubmodule (K := K) W := by
  cases n with
  | zero =>
      exact False.elim (hn (by simp))
  | succ k =>
      have heven : Even k := by
        simpa [Nat.even_add_one] using hn
      exact mem_evenExteriorSubmodule_of_mem_exteriorPower (K := K) (W := W)
        (contractionAction_mem_exteriorPower_pred (K := K) (W := W) d x) heven

/-- Contraction by a covector flips the chosen even summand to the odd one. -/
theorem contractionAction_mem_oddExteriorSubmodule (W : Submodule K V) (d : Module.Dual K W)
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ evenExteriorSubmodule (K := K) W) :
    contractionAction (K := K) W d x ∈ oddExteriorSubmodule (K := K) W := by
  classical
  have hxsum :
      x = Finset.sum (exteriorDecompose (K := K) W x).support
        (fun i =>
          (((exteriorDecompose (K := K) W x) i : ⋀[K]^i W) : IsotropicExteriorModel (K := K) W)) := by
    simpa using (DirectSum.sum_support_decompose (fun i : ℕ => ⋀[K]^i W) x).symm
  rw [hxsum, map_sum]
  exact Submodule.sum_mem _ fun i hi => by
    have hi_even : Even i := by
      by_contra hodd
      exact (DFinsupp.mem_support_iff.mp hi) (hx i hodd)
    exact contractionAction_mem_oddExteriorSubmodule_of_even_degree (K := K) (W := W) d
      (exteriorDecompose (K := K) W x i) hi_even

/-- Contraction by a covector flips the chosen odd summand to the even one. -/
theorem contractionAction_mem_evenExteriorSubmodule (W : Submodule K V) (d : Module.Dual K W)
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ oddExteriorSubmodule (K := K) W) :
    contractionAction (K := K) W d x ∈ evenExteriorSubmodule (K := K) W := by
  classical
  have hxsum :
      x = Finset.sum (exteriorDecompose (K := K) W x).support
        (fun i =>
          (((exteriorDecompose (K := K) W x) i : ⋀[K]^i W) : IsotropicExteriorModel (K := K) W)) := by
    simpa using (DirectSum.sum_support_decompose (fun i : ℕ => ⋀[K]^i W) x).symm
  rw [hxsum, map_sum]
  exact Submodule.sum_mem _ fun i hi => by
    have hiodd : ¬ Even i := by
      intro hieven
      exact (DFinsupp.mem_support_iff.mp hi) (hx i hieven)
    exact contractionAction_mem_evenExteriorSubmodule_of_odd_degree (K := K) (W := W) d
      (exteriorDecompose (K := K) W x i) hiodd

/--
The split generator action of `W* × W` on `⋀W`, given by contraction on the dual factor and
exterior multiplication on the vector factor.
-/
def splitGeneratorAction (W : Submodule K V) :
    Module.Dual K W × W →ₗ[K] Module.End K (IsotropicExteriorModel (K := K) W) :=
  LinearMap.coprod (contractionAction (K := K) W) (wedgeAction (K := K) W)

/-- A split hyperbolic generator sends the chosen even summand to the odd one. -/
theorem splitGeneratorAction_mem_oddExteriorSubmodule (W : Submodule K V) (x : Module.Dual K W × W)
    {y : IsotropicExteriorModel (K := K) W} (hy : y ∈ evenExteriorSubmodule (K := K) W) :
    splitGeneratorAction (K := K) W x y ∈ oddExteriorSubmodule (K := K) W := by
  rcases x with ⟨d, w⟩
  exact Submodule.add_mem _
    (contractionAction_mem_oddExteriorSubmodule (K := K) (W := W) d hy)
    (wedgeAction_mem_oddExteriorSubmodule (K := K) (W := W) w hy)

/-- A split hyperbolic generator sends the chosen odd summand to the even one. -/
theorem splitGeneratorAction_mem_evenExteriorSubmodule (W : Submodule K V) (x : Module.Dual K W × W)
    {y : IsotropicExteriorModel (K := K) W} (hy : y ∈ oddExteriorSubmodule (K := K) W) :
    splitGeneratorAction (K := K) W x y ∈ evenExteriorSubmodule (K := K) W := by
  rcases x with ⟨d, w⟩
  exact Submodule.add_mem _
    (contractionAction_mem_evenExteriorSubmodule (K := K) (W := W) d hy)
    (wedgeAction_mem_evenExteriorSubmodule (K := K) (W := W) w hy)

theorem splitGeneratorAction_sq_apply (W : Submodule K V) (d : Module.Dual K W) (w : W)
    (x : IsotropicExteriorModel (K := K) W) :
    splitGeneratorAction (K := K) W (d, w)
        (splitGeneratorAction (K := K) W (d, w) x) =
      QuadraticForm.dualProd K W (d, w) • x := by
  simp only [splitGeneratorAction, LinearMap.coprod_apply]
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add, map_add]
  rw [contractionAction_sq_apply, wedgeAction_apply, contractionAction_ι_mul,
    wedgeAction_apply, sub_eq_add_neg]
  rw [wedgeAction_apply, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
  abel_nf
  simp [QuadraticForm.dualProd]

/-- The split generator action satisfies the Clifford relation for the hyperbolic form on `W* × W`. -/
theorem splitGeneratorAction_sq (W : Submodule K V) (x : Module.Dual K W × W) :
    splitGeneratorAction (K := K) W x * splitGeneratorAction (K := K) W x =
      algebraMap K (Module.End K (IsotropicExteriorModel (K := K) W))
        ((QuadraticForm.dualProd K W) x) := by
  apply LinearMap.ext
  intro y
  simpa using splitGeneratorAction_sq_apply (K := K) (W := W) (d := x.1) (w := x.2) (x := y)

/--
The induced Clifford action of the split hyperbolic quadratic form on `W* × W`, acting on `⋀W`.
-/
def splitCliffordAction (W : Submodule K V) :
    CliffordAlgebra (QuadraticForm.dualProd K W) →ₐ[K]
      Module.End K (IsotropicExteriorModel (K := K) W) :=
  CliffordAlgebra.lift (QuadraticForm.dualProd K W) ⟨splitGeneratorAction (K := K) W,
    splitGeneratorAction_sq (K := K) (W := W)⟩

instance splitModule (W : Submodule K V) :
    Module (CliffordAlgebra (QuadraticForm.dualProd K W)) (IsotropicExteriorModel (K := K) W) :=
  Module.compHom (IsotropicExteriorModel (K := K) W) (splitCliffordAction (K := K) W).toRingHom

@[simp]
theorem splitCliffordAction_apply_ι (W : Submodule K V) (x : Module.Dual K W × W)
    (y : IsotropicExteriorModel (K := K) W) :
    splitCliffordAction (K := K) W (CliffordAlgebra.ι (QuadraticForm.dualProd K W) x) y =
      splitGeneratorAction (K := K) W x y := by
  rw [splitCliffordAction, CliffordAlgebra.lift_ι_apply]

@[simp]
theorem splitClifford_smul_def (W : Submodule K V)
    (a : CliffordAlgebra (QuadraticForm.dualProd K W))
    (x : IsotropicExteriorModel (K := K) W) :
    a • x = splitCliffordAction (K := K) W a x := rfl

section SplitFaithfulness

variable {I : Type*} [LinearOrder I]

noncomputable def basisMembershipProjectorFactor
    {W : Submodule K V} (b : Module.Basis I K W) (s : Finset I) (i : I) :
    CliffordAlgebra (QuadraticForm.dualProd K W) :=
  if i ∈ s then
    CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, b i) *
      CliffordAlgebra.ι (QuadraticForm.dualProd K W) (b.coord i, 0)
  else
    CliffordAlgebra.ι (QuadraticForm.dualProd K W) (b.coord i, 0) *
      CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, b i)

theorem basisMembershipProjectorFactor_eq
    {W : Submodule K V} (b : Module.Basis I K W) (s : Finset I) (i : I) :
    splitCliffordAction (K := K) W (basisMembershipProjectorFactor (K := K) b s i) =
      basisMembershipProjectorOp (K := K) (W := W) b s i := by
  by_cases his : i ∈ s
  · ext x
    simp [basisMembershipProjectorFactor, basisMembershipProjectorOp, his,
      splitCliffordAction_apply_ι, splitGeneratorAction, map_mul]
  · ext x
    simp [basisMembershipProjectorFactor, basisMembershipProjectorOp, his,
      splitCliffordAction_apply_ι, splitGeneratorAction, map_mul]

noncomputable def basisMembershipProjectorElemAux
    {W : Submodule K V} (b : Module.Basis I K W) (s : Finset I) :
    List I → CliffordAlgebra (QuadraticForm.dualProd K W)
  | [] => 1
  | i :: l =>
      basisMembershipProjectorElemAux b s l *
        basisMembershipProjectorFactor (K := K) b s i

theorem basisMembershipProjectorElemAux_eq
    {W : Submodule K V} (b : Module.Basis I K W) (s : Finset I) :
    ∀ l,
      splitCliffordAction (K := K) W
          (basisMembershipProjectorElemAux (K := K) b s l) =
        basisMembershipProjectorAux (K := K) (W := W) b s l
  | [] => by
      ext x
      simp [basisMembershipProjectorElemAux, basisMembershipProjectorAux]
  | i :: l => by
      rw [basisMembershipProjectorElemAux, basisMembershipProjectorAux, map_mul,
        basisMembershipProjectorElemAux_eq, basisMembershipProjectorFactor_eq,
        Module.End.mul_eq_comp]

noncomputable def basisMembershipProjectorElem
    {W : Submodule K V} [Fintype I] (b : Module.Basis I K W) (s : Finset I) :
    CliffordAlgebra (QuadraticForm.dualProd K W) :=
  basisMembershipProjectorElemAux (K := K) b s ((Finset.univ : Finset I).sort (· ≤ ·))

theorem basisMembershipProjectorElem_apply_basis
    {W : Submodule K V} [Fintype I] (b : Module.Basis I K W) (s t : Finset I) :
    splitCliffordAction (K := K) W
        (basisMembershipProjectorElem (K := K) b s) (b.ExteriorAlgebra t) =
      if t = s then b.ExteriorAlgebra s else 0 := by
  rw [basisMembershipProjectorElem, basisMembershipProjectorElemAux_eq]
  simpa [basisMembershipProjector] using
    basisMembershipProjector_apply_basis (K := K) (W := W) b s t

theorem exists_splitCliffordAction_contract_basis
    {W : Submodule K V} (b : Module.Basis I K W) {i : I} {s : Finset I} (hi : i ∈ s) :
    ∃ a : CliffordAlgebra (QuadraticForm.dualProd K W),
      splitCliffordAction (K := K) W a (b.ExteriorAlgebra s) = b.ExteriorAlgebra (s.erase i) := by
  rcases basis_eq_unit_smul_wedge_basis_erase (K := K) (W := W) (b := b) hi with ⟨c, hc, hs⟩
  have hcontr :
      contractionAction (K := K) W (b.coord i) (b.ExteriorAlgebra s) =
        c • b.ExteriorAlgebra (s.erase i) := by
    rw [hs, map_smul, contractionAction_ι_mul]
    have hzero :
        contractionAction (K := K) W (b.coord i) (b.ExteriorAlgebra (s.erase i)) = 0 := by
      apply contractionAction_basis_eq_zero_of_not_mem (K := K) (W := W) b i
      simp
    simp [hzero]
  refine ⟨algebraMap K _ c *
      CliffordAlgebra.ι (QuadraticForm.dualProd K W) (b.coord i, 0), ?_⟩
  calc
    splitCliffordAction (K := K) W
        (algebraMap K _ c * CliffordAlgebra.ι (QuadraticForm.dualProd K W) (b.coord i, 0))
        (b.ExteriorAlgebra s)
        = c • contractionAction (K := K) W (b.coord i) (b.ExteriorAlgebra s) := by
            simp [map_mul, splitCliffordAction_apply_ι, splitGeneratorAction]
    _ = b.ExteriorAlgebra (s.erase i) := by
          simpa [smul_smul, hc] using congrArg (fun x => c • x) hcontr

theorem exists_splitCliffordAction_wedge_basis
    {W : Submodule K V} (b : Module.Basis I K W) {i : I} {s : Finset I} (hi : i ∉ s) :
    ∃ a : CliffordAlgebra (QuadraticForm.dualProd K W),
      splitCliffordAction (K := K) W a (b.ExteriorAlgebra s) = b.ExteriorAlgebra (insert i s) := by
  rcases basis_eq_unit_smul_wedge_basis_erase (K := K) (W := W) (b := b)
      (i := i) (s := insert i s) (by simp) with ⟨c, hc, hs⟩
  have hs' :
      b.ExteriorAlgebra (insert i s) =
        c • ((ExteriorAlgebra.ι K (b i)) * b.ExteriorAlgebra s) := by
    simpa [hi] using hs
  refine ⟨algebraMap K _ c *
      CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, b i), ?_⟩
  calc
    splitCliffordAction (K := K) W
        (algebraMap K _ c * CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, b i))
        (b.ExteriorAlgebra s)
        = c • wedgeAction (K := K) W (b i) (b.ExteriorAlgebra s) := by
            simp [map_mul, splitCliffordAction_apply_ι, splitGeneratorAction]
    _ = b.ExteriorAlgebra (insert i s) := by
          simpa [wedgeAction_apply] using hs'.symm

theorem exists_splitCliffordAction_remove_basis
    {W : Submodule K V} (b : Module.Basis I K W) (r t : Finset I) (hr : r ⊆ t) :
    ∃ a : CliffordAlgebra (QuadraticForm.dualProd K W),
      splitCliffordAction (K := K) W a (b.ExteriorAlgebra t) = b.ExteriorAlgebra (t \ r) := by
  induction r using Finset.induction_on generalizing t with
  | empty =>
      refine ⟨1, ?_⟩
      simp
  | @insert i r hir ih =>
      have hit : i ∈ t := hr (by simp)
      rcases exists_splitCliffordAction_contract_basis (K := K) (W := W) b hit with ⟨ai, hai⟩
      have hrt : r ⊆ t.erase i := by
        intro j hj
        have hjt : j ∈ t := hr (by simp [hj])
        have hji : j ≠ i := by
          intro hji
          subst hji
          exact hir hj
        simp [hjt, hji]
      rcases ih (t.erase i) hrt with ⟨ar, har⟩
      refine ⟨ar * ai, ?_⟩
      calc
        splitCliffordAction (K := K) W (ar * ai) (b.ExteriorAlgebra t)
            = splitCliffordAction (K := K) W ar (b.ExteriorAlgebra (t.erase i)) := by
                simp [map_mul, hai]
        _ = b.ExteriorAlgebra ((t.erase i) \ r) := har
        _ = b.ExteriorAlgebra (t \ insert i r) := by
              congr 1
              ext j
              simp [and_left_comm, and_assoc]

theorem exists_splitCliffordAction_add_basis
    {W : Submodule K V} (b : Module.Basis I K W) (r t : Finset I) (hr : Disjoint r t) :
    ∃ a : CliffordAlgebra (QuadraticForm.dualProd K W),
      splitCliffordAction (K := K) W a (b.ExteriorAlgebra t) = b.ExteriorAlgebra (t ∪ r) := by
  induction r using Finset.induction_on generalizing t with
  | empty =>
      refine ⟨1, ?_⟩
      simp
  | @insert i r hir ih =>
      have hrt : Disjoint r t := by
        rw [Finset.disjoint_left] at hr ⊢
        intro j hjr hjt
        exact hr (by simp [hjr]) hjt
      rcases ih t hrt with ⟨ar, har⟩
      have hit : i ∉ t := by
        rw [Finset.disjoint_left] at hr
        exact fun hit => hr (by simp) hit
      have hi_union : i ∉ t ∪ r := by
        simp [hit, hir]
      rcases exists_splitCliffordAction_wedge_basis (K := K) (W := W) b hi_union with ⟨ai, hai⟩
      refine ⟨ai * ar, ?_⟩
      calc
        splitCliffordAction (K := K) W (ai * ar) (b.ExteriorAlgebra t)
            = splitCliffordAction (K := K) W ai (b.ExteriorAlgebra (t ∪ r)) := by
                simp [map_mul, har]
        _ = b.ExteriorAlgebra (insert i (t ∪ r)) := hai
        _ = b.ExteriorAlgebra (t ∪ insert i r) := by
              congr 1
              ext j
              simp

theorem exists_splitCliffordAction_basis_transfer
    {W : Submodule K V} (b : Module.Basis I K W) (s t : Finset I) :
    ∃ a : CliffordAlgebra (QuadraticForm.dualProd K W),
      splitCliffordAction (K := K) W a (b.ExteriorAlgebra t) = b.ExteriorAlgebra s := by
  let r₁ := t \ s
  rcases exists_splitCliffordAction_remove_basis (K := K) (W := W) b r₁ t (by
      intro i hi
      simp [r₁] at hi
      exact hi.1) with ⟨ar, har⟩
  rcases exists_splitCliffordAction_add_basis (K := K) (W := W) b (s \ t) (t ∩ s) (by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      simp at hi1 hi2
      exact hi1.2 hi2.1) with ⟨aa, haa⟩
  refine ⟨aa * ar, ?_⟩
  calc
    splitCliffordAction (K := K) W (aa * ar) (b.ExteriorAlgebra t)
        = splitCliffordAction (K := K) W aa (b.ExteriorAlgebra (t \ r₁)) := by
            simp [map_mul, har]
    _ = splitCliffordAction (K := K) W aa (b.ExteriorAlgebra (t ∩ s)) := by
          have hts : t \ r₁ = t ∩ s := by
            ext i
            simp [r₁]
          simp [hts]
    _ = b.ExteriorAlgebra ((t ∩ s) ∪ (s \ t)) := haa
    _ = b.ExteriorAlgebra s := by
          congr 1
          ext i
          by_cases hit : i ∈ t <;> simp [hit]

theorem exists_splitCliffordAction_eq_basisEnd
    {W : Submodule K V} [Fintype I] (b : Module.Basis I K W) (s t : Finset I) :
    ∃ a : CliffordAlgebra (QuadraticForm.dualProd K W),
      splitCliffordAction (K := K) W a = (b.ExteriorAlgebra).end (s, t) := by
  rcases exists_splitCliffordAction_basis_transfer (K := K) (W := W) b s t with ⟨a, ha⟩
  refine ⟨a * basisMembershipProjectorElem (K := K) b t, ?_⟩
  apply (b.ExteriorAlgebra).ext
  intro u
  by_cases hut : u = t
  · subst hut
    rw [map_mul, Module.End.mul_eq_comp]
    change
      ((splitCliffordAction (K := K) W) a)
        (((splitCliffordAction (K := K) W) (basisMembershipProjectorElem (K := K) b u))
          (b.ExteriorAlgebra u)) =
        ((b.ExteriorAlgebra).end (s, u)) (b.ExteriorAlgebra u)
    rw [basisMembershipProjectorElem_apply_basis, if_pos rfl, ha]
    simpa using ((b.ExteriorAlgebra).end_apply_apply (s, u) u).symm
  · have hend :
        ((b.ExteriorAlgebra).end (s, t)) (b.ExteriorAlgebra u) = 0 := by
          have htu : t ≠ u := by
            intro htu
            exact hut htu.symm
          simpa [htu] using (b.ExteriorAlgebra.end_apply_apply (s, t) u)
    rw [map_mul, Module.End.mul_eq_comp]
    change
      ((splitCliffordAction (K := K) W) a)
        (((splitCliffordAction (K := K) W) (basisMembershipProjectorElem (K := K) b t))
          (b.ExteriorAlgebra u)) =
        ((b.ExteriorAlgebra).end (s, t)) (b.ExteriorAlgebra u)
    simp [basisMembershipProjectorElem_apply_basis, hut, hend]

theorem splitCliffordAction_surjective
    {W : Submodule K V} [Fintype I] (b : Module.Basis I K W) :
    Function.Surjective (splitCliffordAction (K := K) W) := by
  let bE := b.ExteriorAlgebra
  have hspan :
      Submodule.span K (Set.range bE.end) ≤ LinearMap.range (splitCliffordAction (K := K) W).toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro f ⟨st, rfl⟩
    rcases exists_splitCliffordAction_eq_basisEnd (K := K) (W := W) b st.1 st.2 with ⟨a, ha⟩
    exact ⟨a, by simpa using ha⟩
  have htop : (⊤ : Submodule K (Module.End K (IsotropicExteriorModel (K := K) W))) ≤
      LinearMap.range (splitCliffordAction (K := K) W).toLinearMap := by
    rw [← bE.end.span_eq]
    exact hspan
  exact LinearMap.range_eq_top.mp (le_antisymm le_top htop)

omit [Invertible (2 : K)] in
theorem splitCliffordAction_finrank_eq
    {W : Submodule K V} [Fintype I] [Invertible (2 : K)] (b : Module.Basis I K W) :
    Module.finrank K (CliffordAlgebra (QuadraticForm.dualProd K W)) =
      Module.finrank K (Module.End K (IsotropicExteriorModel (K := K) W)) := by
  classical
  letI : LinearOrder (I ⊕ I) := linearOrderOfSTO WellOrderingRel
  let bCl :
      Module.Basis (Finset I × Finset I) K (CliffordAlgebra (QuadraticForm.dualProd K W)) :=
    (((b.dualBasis.prod b).ExteriorAlgebra.map
      (CliffordAlgebra.equivExterior (QuadraticForm.dualProd K W)).symm).reindex
        Finset.sumEquiv.toEquiv)
  let bEnd : Module.Basis (Finset I × Finset I) K
      (Module.End K (IsotropicExteriorModel (K := K) W)) :=
    (b.ExteriorAlgebra).end
  letI := bCl.finiteDimensional_of_finite
  letI := bEnd.finiteDimensional_of_finite
  rw [Module.finrank_eq_card_basis bCl, Module.finrank_eq_card_basis bEnd]

omit [Invertible (2 : K)] in
theorem splitCliffordAction_injective
    {W : Submodule K V} [Fintype I] [Invertible (2 : K)] (b : Module.Basis I K W) :
    Function.Injective (splitCliffordAction (K := K) W) := by
  classical
  letI : LinearOrder (I ⊕ I) := linearOrderOfSTO WellOrderingRel
  let bCl :
      Module.Basis (Finset I × Finset I) K (CliffordAlgebra (QuadraticForm.dualProd K W)) :=
    (((b.dualBasis.prod b).ExteriorAlgebra.map
      (CliffordAlgebra.equivExterior (QuadraticForm.dualProd K W)).symm).reindex
        Finset.sumEquiv.toEquiv)
  let bEnd : Module.Basis (Finset I × Finset I) K
      (Module.End K (IsotropicExteriorModel (K := K) W)) :=
    (b.ExteriorAlgebra).end
  letI := bCl.finiteDimensional_of_finite
  letI := bEnd.finiteDimensional_of_finite
  have hdim := splitCliffordAction_finrank_eq (K := K) (W := W) b
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (splitCliffordAction (K := K) W).toLinearMap) hdim).mpr
    (splitCliffordAction_surjective (K := K) (W := W) b)

end SplitFaithfulness

section SplitIrreducibility

variable [FiniteDimensional K V]

/-- Because the split chosen-model Clifford action hits the full endomorphism algebra of `⋀W`, the
split `Cl(W* × W)`-module `⋀W` is simple. -/
theorem splitCliffordAction_isSimpleModule (W : Submodule K V) :
    IsSimpleModule (CliffordAlgebra (QuadraticForm.dualProd K W))
      (IsotropicExteriorModel (K := K) W) := by
  classical
  let b := Module.finBasis K W
  let σ : CliffordAlgebra (QuadraticForm.dualProd K W) →+*
      Module.End K (IsotropicExteriorModel (K := K) W) :=
    (splitCliffordAction (K := K) W).toRingHom
  letI : RingHomSurjective σ := ⟨splitCliffordAction_surjective (K := K) (W := W) b⟩
  let l :
      IsotropicExteriorModel (K := K) W →ₛₗ[σ]
        IsotropicExteriorModel (K := K) W :=
    { toFun := id
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        simp [σ, splitClifford_smul_def] }
  exact
    (LinearMap.isSimpleModule_iff_of_bijective (σ := σ) (l := l)
      (by simpa [l] using Function.bijective_id)).2 inferInstance

end SplitIrreducibility

/-- Odd split Clifford elements send the chosen even summand of `⋀W` to the odd one. -/
theorem splitCliffordAction_mem_oddExteriorSubmodule_of_odd (W : Submodule K V)
    {a : CliffordAlgebra (QuadraticForm.dualProd K W)}
    (ha : a ∈ CliffordAlgebra.evenOdd (QuadraticForm.dualProd K W) 1)
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ evenExteriorSubmodule (K := K) W) :
    splitCliffordAction (K := K) W a x ∈ oddExteriorSubmodule (K := K) W := by
  have hpres :
      ∀ {b : CliffordAlgebra (QuadraticForm.dualProd K W)},
        b ∈ CliffordAlgebra.evenOdd (QuadraticForm.dualProd K W) 1 →
        ∀ y : IsotropicExteriorModel (K := K) W,
          y ∈ evenExteriorSubmodule (K := K) W →
          splitCliffordAction (K := K) W b y ∈ oddExteriorSubmodule (K := K) W := by
    intro b hb
    refine CliffordAlgebra.odd_induction (Q := QuadraticForm.dualProd K W) ?_ ?_ ?_ b hb
    · intro m y hy
      simpa [splitCliffordAction_apply_ι] using
        splitGeneratorAction_mem_oddExteriorSubmodule (K := K) (W := W) m hy
    · intro b c hb hc ihb ihc y hy
      simpa [map_add, LinearMap.add_apply] using
        Submodule.add_mem (oddExteriorSubmodule (K := K) W) (ihb y hy) (ihc y hy)
    · intro m₁ m₂ b hb ih y hy
      simp [splitCliffordAction_apply_ι, map_mul]
      exact splitGeneratorAction_mem_oddExteriorSubmodule (K := K) (W := W) m₁
        (splitGeneratorAction_mem_evenExteriorSubmodule (K := K) (W := W) m₂ (ih y hy))
  exact hpres ha x hx

/-- Odd split Clifford elements send the chosen odd summand of `⋀W` to the even one. -/
theorem splitCliffordAction_mem_evenExteriorSubmodule_of_odd (W : Submodule K V)
    {a : CliffordAlgebra (QuadraticForm.dualProd K W)}
    (ha : a ∈ CliffordAlgebra.evenOdd (QuadraticForm.dualProd K W) 1)
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ oddExteriorSubmodule (K := K) W) :
    splitCliffordAction (K := K) W a x ∈ evenExteriorSubmodule (K := K) W := by
  have hpres :
      ∀ {b : CliffordAlgebra (QuadraticForm.dualProd K W)},
        b ∈ CliffordAlgebra.evenOdd (QuadraticForm.dualProd K W) 1 →
        ∀ y : IsotropicExteriorModel (K := K) W,
          y ∈ oddExteriorSubmodule (K := K) W →
          splitCliffordAction (K := K) W b y ∈ evenExteriorSubmodule (K := K) W := by
    intro b hb
    refine CliffordAlgebra.odd_induction (Q := QuadraticForm.dualProd K W) ?_ ?_ ?_ b hb
    · intro m y hy
      simpa [splitCliffordAction_apply_ι] using
        splitGeneratorAction_mem_evenExteriorSubmodule (K := K) (W := W) m hy
    · intro b c hb hc ihb ihc y hy
      simpa [map_add, LinearMap.add_apply] using
        Submodule.add_mem (evenExteriorSubmodule (K := K) W) (ihb y hy) (ihc y hy)
    · intro m₁ m₂ b hb ih y hy
      simp [splitCliffordAction_apply_ι, map_mul]
      simpa [mem_evenExteriorSubmodule_iff, Nat.not_even_iff_odd] using
        (splitGeneratorAction_mem_evenExteriorSubmodule (K := K) (W := W) m₁
          (splitGeneratorAction_mem_oddExteriorSubmodule (K := K) (W := W) m₂ (ih y hy)))
  exact hpres ha x hx

/-- Even split Clifford elements preserve the chosen even summand of `⋀W`. -/
theorem splitCliffordAction_mem_evenExteriorSubmodule (W : Submodule K V)
    {a : CliffordAlgebra (QuadraticForm.dualProd K W)}
    (ha : a ∈ CliffordAlgebra.evenOdd (QuadraticForm.dualProd K W) 0)
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ evenExteriorSubmodule (K := K) W) :
    splitCliffordAction (K := K) W a x ∈ evenExteriorSubmodule (K := K) W := by
  have hpres :
      ∀ {b : CliffordAlgebra (QuadraticForm.dualProd K W)},
        b ∈ CliffordAlgebra.evenOdd (QuadraticForm.dualProd K W) 0 →
        ∀ y : IsotropicExteriorModel (K := K) W,
          y ∈ evenExteriorSubmodule (K := K) W →
          splitCliffordAction (K := K) W b y ∈ evenExteriorSubmodule (K := K) W := by
    intro b hb
    refine CliffordAlgebra.even_induction (Q := QuadraticForm.dualProd K W) ?_ ?_ ?_ b hb
    · intro r y hy
      simpa [splitClifford_smul_def] using
        Submodule.smul_mem (evenExteriorSubmodule (K := K) W) r hy
    · intro b c hb hc ihb ihc y hy
      simpa [map_add, LinearMap.add_apply] using
        Submodule.add_mem (evenExteriorSubmodule (K := K) W) (ihb y hy) (ihc y hy)
    · intro m₁ m₂ b hb ih y hy
      simp [splitCliffordAction_apply_ι, map_mul]
      simpa [mem_evenExteriorSubmodule_iff, Nat.not_even_iff_odd] using
        (splitGeneratorAction_mem_evenExteriorSubmodule (K := K) (W := W) m₁
          (splitGeneratorAction_mem_oddExteriorSubmodule (K := K) (W := W) m₂ (ih y hy)))
  exact hpres ha x hx

/-- Even split Clifford elements preserve the chosen odd summand of `⋀W`. -/
theorem splitCliffordAction_mem_oddExteriorSubmodule (W : Submodule K V)
    {a : CliffordAlgebra (QuadraticForm.dualProd K W)}
    (ha : a ∈ CliffordAlgebra.evenOdd (QuadraticForm.dualProd K W) 0)
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ oddExteriorSubmodule (K := K) W) :
    splitCliffordAction (K := K) W a x ∈ oddExteriorSubmodule (K := K) W := by
  have hpres :
      ∀ {b : CliffordAlgebra (QuadraticForm.dualProd K W)},
        b ∈ CliffordAlgebra.evenOdd (QuadraticForm.dualProd K W) 0 →
        ∀ y : IsotropicExteriorModel (K := K) W,
          y ∈ oddExteriorSubmodule (K := K) W →
          splitCliffordAction (K := K) W b y ∈ oddExteriorSubmodule (K := K) W := by
    intro b hb
    refine CliffordAlgebra.even_induction (Q := QuadraticForm.dualProd K W) ?_ ?_ ?_ b hb
    · intro r y hy
      simpa [splitClifford_smul_def] using
        Submodule.smul_mem (oddExteriorSubmodule (K := K) W) r hy
    · intro b c hb hc ihb ihc y hy
      simpa [map_add, LinearMap.add_apply] using
        Submodule.add_mem (oddExteriorSubmodule (K := K) W) (ihb y hy) (ihc y hy)
    · intro m₁ m₂ b hb ih y hy
      simp [splitCliffordAction_apply_ι, map_mul]
      simpa [mem_oddExteriorSubmodule_iff] using
        (splitGeneratorAction_mem_oddExteriorSubmodule (K := K) (W := W) m₁
          (splitGeneratorAction_mem_evenExteriorSubmodule (K := K) (W := W) m₂ (ih y hy)))
  exact hpres ha x hx

/-- The split Clifford action restricted to the even Clifford part and the chosen even half. -/
noncomputable def evenSplitCliffordAction (W : Submodule K V) :
    CliffordAlgebra.even (QuadraticForm.dualProd K W) →ₐ[K]
      Module.End K (evenExteriorSubmodule (K := K) W) where
  toFun a :=
    LinearMap.restrict (splitCliffordAction (K := K) W a.1)
      (fun x hx => splitCliffordAction_mem_evenExteriorSubmodule (K := K) (W := W) a.2 hx)
  map_zero' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_add' := by
    intro a b
    ext x
    simp [LinearMap.restrict_apply, map_add]
  map_one' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_mul' := by
    intro a b
    ext x
    simp [LinearMap.restrict_apply]
  commutes' := by
    intro r
    ext x
    simp [LinearMap.restrict_apply]

/-- The split Clifford action restricted to the even Clifford part and the chosen odd half. -/
noncomputable def oddSplitCliffordAction (W : Submodule K V) :
    CliffordAlgebra.even (QuadraticForm.dualProd K W) →ₐ[K]
      Module.End K (oddExteriorSubmodule (K := K) W) where
  toFun a :=
    LinearMap.restrict (splitCliffordAction (K := K) W a.1)
      (fun x hx => splitCliffordAction_mem_oddExteriorSubmodule (K := K) (W := W) a.2 hx)
  map_zero' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_add' := by
    intro a b
    ext x
    simp [LinearMap.restrict_apply, map_add]
  map_one' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_mul' := by
    intro a b
    ext x
    simp [LinearMap.restrict_apply]
  commutes' := by
    intro r
    ext x
    simp [LinearMap.restrict_apply]

/-- The chosen even half of `⋀W` is a module over the even split Clifford algebra. -/
noncomputable abbrev evenSplitCliffordModule (W : Submodule K V) :
    Module (CliffordAlgebra.even (QuadraticForm.dualProd K W))
      (evenExteriorSubmodule (K := K) W) :=
  Module.compHom (evenExteriorSubmodule (K := K) W)
    (evenSplitCliffordAction (K := K) W).toRingHom

/-- The chosen odd half of `⋀W` is a module over the even split Clifford algebra. -/
noncomputable abbrev oddSplitCliffordModule (W : Submodule K V) :
    Module (CliffordAlgebra.even (QuadraticForm.dualProd K W))
      (oddExteriorSubmodule (K := K) W) :=
  Module.compHom (oddExteriorSubmodule (K := K) W)
    (oddSplitCliffordAction (K := K) W).toRingHom

@[simp]
theorem evenSplitClifford_smul_def (W : Submodule K V)
    (a : CliffordAlgebra.even (QuadraticForm.dualProd K W))
    (x : evenExteriorSubmodule (K := K) W) :
    letI := evenSplitCliffordModule (K := K) W
    a • x = evenSplitCliffordAction (K := K) W a x := rfl

@[simp]
theorem oddSplitClifford_smul_def (W : Submodule K V)
    (a : CliffordAlgebra.even (QuadraticForm.dualProd K W))
    (x : oddExteriorSubmodule (K := K) W) :
    letI := oddSplitCliffordModule (K := K) W
    a • x = oddSplitCliffordAction (K := K) W a x := rfl

section SplitHalfIrreducibility

variable [FiniteDimensional K V]

/-- The chosen even half of `⋀W` is simple under the even split Clifford action. -/
theorem evenSplitCliffordAction_isSimpleModule (W : Submodule K V) :
    letI := evenSplitCliffordModule (K := K) W
    IsSimpleModule (CliffordAlgebra.even (QuadraticForm.dualProd K W))
      (evenExteriorSubmodule (K := K) W) := by
  classical
  letI := evenSplitCliffordModule (K := K) W
  let hone : evenExteriorSubmodule (K := K) W := ⟨1, by
    refine (mem_evenExteriorSubmodule_of_mem_exteriorPower (K := K) (W := W)
      (n := 0) (x := (1 : IsotropicExteriorModel (K := K) W))) ?_ (by simp)
    change (1 : IsotropicExteriorModel (K := K) W) ∈
      (LinearMap.range (ExteriorAlgebra.ι K : W →ₗ[K] IsotropicExteriorModel (K := K) W) ^ 0)
    simp
  ⟩
  have hone_ne : hone ≠ 0 := by
    intro h
    have h' : (hone : IsotropicExteriorModel (K := K) W) = 0 := congrArg Subtype.val h
    exact one_ne_zero h'
  letI : Nontrivial (evenExteriorSubmodule (K := K) W) := ⟨⟨0, hone, fun h => hone_ne h.symm⟩⟩
  have hsimpleFull := splitCliffordAction_isSimpleModule (K := K) (W := W)
  have hsurjFull :=
    (isSimpleModule_iff_toSpanSingleton_surjective
      (R := CliffordAlgebra (QuadraticForm.dualProd K W))
      (M := IsotropicExteriorModel (K := K) W)).mp hsimpleFull
  refine
    (isSimpleModule_iff_toSpanSingleton_surjective
      (R := CliffordAlgebra.even (QuadraticForm.dualProd K W))
      (M := evenExteriorSubmodule (K := K) W)).mpr ?_
  refine ⟨inferInstance, ?_⟩
  intro x hx y
  have hx' : (x : IsotropicExteriorModel (K := K) W) ≠ 0 := by
    intro h
    apply hx
    ext
    exact h
  obtain ⟨a, ha⟩ := hsurjFull.2 (x : IsotropicExteriorModel (K := K) W) hx'
    (y : IsotropicExteriorModel (K := K) W)
  have haAct :
      splitCliffordAction (K := K) W a x = y := by
    simpa [splitClifford_smul_def] using ha
  obtain ⟨aEven, aOdd, haDecomp, _⟩ := Submodule.existsUnique_add_of_isCompl
    (CliffordAlgebra.evenOdd_isCompl (Q := QuadraticForm.dualProd K W)) a
  have hEven :
      splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x ∈
        evenExteriorSubmodule (K := K) W :=
    splitCliffordAction_mem_evenExteriorSubmodule (K := K) (W := W) aEven.2 x.2
  have hOdd :
      splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x ∈
        oddExteriorSubmodule (K := K) W :=
    splitCliffordAction_mem_oddExteriorSubmodule_of_odd (K := K) (W := W)
      aOdd.2 x.2
  have hsum :
      splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
          splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
        y := by
    calc
      splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
          splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
        splitCliffordAction (K := K) W
          ((aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) +
            (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W))) x := by
            symm
            exact congrArg
              (fun f : Module.End K (IsotropicExteriorModel (K := K) W) => f x)
              ((splitCliffordAction (K := K) W).map_add
                (aEven : CliffordAlgebra (QuadraticForm.dualProd K W))
                (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)))
      _ = splitCliffordAction (K := K) W a x := by
            simpa using congrArg (fun z : CliffordAlgebra (QuadraticForm.dualProd K W) =>
              splitCliffordAction (K := K) W z x) haDecomp
      _ = y := haAct
  obtain ⟨u, v, _huv, huniqY⟩ := Submodule.existsUnique_add_of_isCompl
    (evenExteriorSubmodule_isCompl (K := K) (W := W)) (y : IsotropicExteriorModel (K := K) W)
  have huv0' : y = u ∧ (0 : oddExteriorSubmodule (K := K) W) = v := by
    simpa using huniqY y 0 (by simp)
  have huv0 : u = y ∧ v = 0 := ⟨huv0'.1.symm, huv0'.2.symm⟩
  have huvs :
      (⟨splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
          hEven⟩ : evenExteriorSubmodule (K := K) W) = u ∧
        (⟨splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
          hOdd⟩ : oddExteriorSubmodule (K := K) W) = v := by
    exact huniqY
      ⟨splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
        hEven⟩
      ⟨splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
        hOdd⟩
      hsum
  have hAct :
      splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
        y := by
    exact congrArg Subtype.val (huvs.1.trans huv0.1)
  refine ⟨aEven, ?_⟩
  simpa [LinearMap.toSpanSingleton_apply, evenSplitClifford_smul_def] using (Subtype.ext hAct)

/-- For positive split rank, the chosen odd half of `⋀W` is simple under the even split Clifford
action. -/
theorem oddSplitCliffordAction_isSimpleModule (W : Submodule K V)
    (hW : 0 < Module.finrank K W) :
    letI := oddSplitCliffordModule (K := K) W
    IsSimpleModule (CliffordAlgebra.even (QuadraticForm.dualProd K W))
      (oddExteriorSubmodule (K := K) W) := by
  classical
  letI := oddSplitCliffordModule (K := K) W
  let b := Module.finBasis K W
  let i : Fin (Module.finrank K W) := ⟨0, hW⟩
  let hodd : oddExteriorSubmodule (K := K) W := ⟨ExteriorAlgebra.ι K (b i), by
    refine (mem_oddExteriorSubmodule_of_mem_exteriorPower (K := K) (W := W)
      (n := 1) (x := ExteriorAlgebra.ι K (b i))) ?_ ?_
    · change ExteriorAlgebra.ι K (b i) ∈
        (LinearMap.range (ExteriorAlgebra.ι K : W →ₗ[K] IsotropicExteriorModel (K := K) W) ^ 1)
      rw [pow_one]
      exact
        LinearMap.mem_range_self
          (ExteriorAlgebra.ι K : W →ₗ[K] IsotropicExteriorModel (K := K) W) (b i)
    · simp
  ⟩
  have hodd_ne : hodd ≠ 0 := by
    intro h
    have h' : (hodd : IsotropicExteriorModel (K := K) W) = 0 := congrArg Subtype.val h
    exact b.ne_zero i ((ExteriorAlgebra.ι_eq_zero_iff (R := K) (x := b i)).mp h')
  letI : Nontrivial (oddExteriorSubmodule (K := K) W) := ⟨⟨0, hodd, fun h => hodd_ne h.symm⟩⟩
  have hsimpleFull := splitCliffordAction_isSimpleModule (K := K) (W := W)
  have hsurjFull :=
    (isSimpleModule_iff_toSpanSingleton_surjective
      (R := CliffordAlgebra (QuadraticForm.dualProd K W))
      (M := IsotropicExteriorModel (K := K) W)).mp hsimpleFull
  refine
    (isSimpleModule_iff_toSpanSingleton_surjective
      (R := CliffordAlgebra.even (QuadraticForm.dualProd K W))
      (M := oddExteriorSubmodule (K := K) W)).mpr ?_
  refine ⟨inferInstance, ?_⟩
  intro x hx y
  have hx' : (x : IsotropicExteriorModel (K := K) W) ≠ 0 := by
    intro h
    apply hx
    ext
    exact h
  obtain ⟨a, ha⟩ := hsurjFull.2 (x : IsotropicExteriorModel (K := K) W) hx'
    (y : IsotropicExteriorModel (K := K) W)
  have haAct :
      splitCliffordAction (K := K) W a x = y := by
    simpa [splitClifford_smul_def] using ha
  obtain ⟨aEven, aOdd, haDecomp, _⟩ := Submodule.existsUnique_add_of_isCompl
    (CliffordAlgebra.evenOdd_isCompl (Q := QuadraticForm.dualProd K W)) a
  have hOdd :
      splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x ∈
        oddExteriorSubmodule (K := K) W :=
    splitCliffordAction_mem_oddExteriorSubmodule (K := K) (W := W) aEven.2 x.2
  have hEven :
      splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x ∈
        evenExteriorSubmodule (K := K) W :=
    splitCliffordAction_mem_evenExteriorSubmodule_of_odd (K := K) (W := W)
      aOdd.2 x.2
  have hsum :
      splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
          splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
        y := by
    calc
      splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
          splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
        splitCliffordAction (K := K) W
          ((aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) +
            (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W))) x := by
            symm
            exact congrArg
              (fun f : Module.End K (IsotropicExteriorModel (K := K) W) => f x)
              ((splitCliffordAction (K := K) W).map_add
                (aEven : CliffordAlgebra (QuadraticForm.dualProd K W))
                (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)))
      _ = splitCliffordAction (K := K) W a x := by
            simpa using congrArg (fun z : CliffordAlgebra (QuadraticForm.dualProd K W) =>
              splitCliffordAction (K := K) W z x) haDecomp
      _ = y := haAct
  obtain ⟨u, v, _huv, huniqY⟩ := Submodule.existsUnique_add_of_isCompl
    (evenExteriorSubmodule_isCompl (K := K) (W := W)) (y : IsotropicExteriorModel (K := K) W)
  have huv0' : (0 : evenExteriorSubmodule (K := K) W) = u ∧ y = v := by
    simpa using huniqY 0 y (by simp)
  have huv0 : u = 0 ∧ v = y := ⟨huv0'.1.symm, huv0'.2.symm⟩
  have hsum' :
      splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
          splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
        y := by
    simpa [add_comm] using hsum
  have huvs :
      (⟨splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
          hEven⟩ : evenExteriorSubmodule (K := K) W) = u ∧
        (⟨splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
          hOdd⟩ : oddExteriorSubmodule (K := K) W) = v := by
    exact huniqY
      ⟨splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
        hEven⟩
      ⟨splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
        hOdd⟩
      hsum'
  have hAct :
      splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
        y := by
    exact congrArg Subtype.val (huvs.2.trans huv0.2)
  refine ⟨aEven, ?_⟩
  simpa [LinearMap.toSpanSingleton_apply, oddSplitClifford_smul_def] using (Subtype.ext hAct)

end SplitHalfIrreducibility

section SplitHalfInequivalence

variable [FiniteDimensional K V]

/-- The even split Clifford algebra contains an element acting as the projector onto the chosen even
half of `⋀W`. -/
theorem exists_evenSplitCliffordParityProjector (W : Submodule K V) :
    ∃ a : CliffordAlgebra.even (QuadraticForm.dualProd K W),
      (∀ x : evenExteriorSubmodule (K := K) W,
        evenSplitCliffordAction (K := K) W a x = x) ∧
      ∀ x : oddExteriorSubmodule (K := K) W,
        oddSplitCliffordAction (K := K) W a x = 0 := by
  classical
  let b := Module.finBasis K W
  let p : Module.End K (IsotropicExteriorModel (K := K) W) :=
    Submodule.IsCompl.projection (evenExteriorSubmodule_isCompl (K := K) (W := W))
  obtain ⟨a, ha⟩ := splitCliffordAction_surjective (K := K) (W := W) b p
  obtain ⟨aEven, aOdd, haDecomp, _⟩ := Submodule.existsUnique_add_of_isCompl
    (CliffordAlgebra.evenOdd_isCompl (Q := QuadraticForm.dualProd K W)) a
  refine ⟨aEven, ?_, ?_⟩
  · intro x
    have hEven :
        splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x ∈
          evenExteriorSubmodule (K := K) W :=
      splitCliffordAction_mem_evenExteriorSubmodule (K := K) (W := W) aEven.2 x.2
    have hOdd :
        splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x ∈
          oddExteriorSubmodule (K := K) W :=
      splitCliffordAction_mem_oddExteriorSubmodule_of_odd (K := K) (W := W) aOdd.2 x.2
    have hsum :
      splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
          splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
          x := by
        calc
          splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
              splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
            splitCliffordAction (K := K) W
              ((aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) +
                (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W))) x := by
              symm
              exact congrArg
                (fun f : Module.End K (IsotropicExteriorModel (K := K) W) => f x)
                ((splitCliffordAction (K := K) W).map_add
                  (aEven : CliffordAlgebra (QuadraticForm.dualProd K W))
                  (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)))
        _ = splitCliffordAction (K := K) W a x := by
              simpa using congrArg (fun z : CliffordAlgebra (QuadraticForm.dualProd K W) =>
                splitCliffordAction (K := K) W z x) haDecomp
        _ = p x := by
              simpa [p] using congrArg
                (fun f : Module.End K (IsotropicExteriorModel (K := K) W) => f x) ha
        _ = x := by
              change
                Submodule.IsCompl.projection
                    (evenExteriorSubmodule_isCompl (K := K) (W := W)) x = x
              exact
                Submodule.IsCompl.projection_apply_left
                  (evenExteriorSubmodule_isCompl (K := K) (W := W)) x
    obtain ⟨u, v, _huv, huniqX⟩ := Submodule.existsUnique_add_of_isCompl
      (evenExteriorSubmodule_isCompl (K := K) (W := W)) (x : IsotropicExteriorModel (K := K) W)
    have huv0' : x = u ∧ (0 : oddExteriorSubmodule (K := K) W) = v := by
      simpa using huniqX x 0 (by simp)
    have huv0 : u = x ∧ v = 0 := ⟨huv0'.1.symm, huv0'.2.symm⟩
    have huvs :
        (⟨splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
            hEven⟩ : evenExteriorSubmodule (K := K) W) = u ∧
          (⟨splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
            hOdd⟩ : oddExteriorSubmodule (K := K) W) = v := by
      exact huniqX
        ⟨splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
          hEven⟩
        ⟨splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
          hOdd⟩
        hsum
    have hAct :
        splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
          x := by
      exact congrArg Subtype.val (huvs.1.trans huv0.1)
    simpa [evenSplitClifford_smul_def] using (Subtype.ext hAct)
  · intro x
    have hOdd :
        splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x ∈
          oddExteriorSubmodule (K := K) W :=
      splitCliffordAction_mem_oddExteriorSubmodule (K := K) (W := W) aEven.2 x.2
    have hEven :
        splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x ∈
          evenExteriorSubmodule (K := K) W :=
      splitCliffordAction_mem_evenExteriorSubmodule_of_odd (K := K) (W := W) aOdd.2 x.2
    have hsum :
      splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
          splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
          0 := by
      calc
        splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
            splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
          splitCliffordAction (K := K) W
            ((aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) +
              (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W))) x := by
              symm
              exact congrArg
                (fun f : Module.End K (IsotropicExteriorModel (K := K) W) => f x)
                ((splitCliffordAction (K := K) W).map_add
                  (aEven : CliffordAlgebra (QuadraticForm.dualProd K W))
                  (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)))
        _ = splitCliffordAction (K := K) W a x := by
              simpa using congrArg (fun z : CliffordAlgebra (QuadraticForm.dualProd K W) =>
                splitCliffordAction (K := K) W z x) haDecomp
        _ = p x := by
              simpa [p] using congrArg
                (fun f : Module.End K (IsotropicExteriorModel (K := K) W) => f x) ha
        _ = 0 := by
              change
                Submodule.IsCompl.projection
                    (evenExteriorSubmodule_isCompl (K := K) (W := W)) x = 0
              exact
                (Submodule.IsCompl.projection_apply_eq_zero_iff
                  (evenExteriorSubmodule_isCompl (K := K) (W := W))).2 x.2
    have hsum' :
        splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
            splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
          0 := by
      simpa [add_comm] using hsum
    obtain ⟨u, v, _huv, huniq0⟩ := Submodule.existsUnique_add_of_isCompl
      (evenExteriorSubmodule_isCompl (K := K) (W := W)) (0 : IsotropicExteriorModel (K := K) W)
    have huv0' :
        (0 : evenExteriorSubmodule (K := K) W) = u ∧
          (0 : oddExteriorSubmodule (K := K) W) = v := by
      simpa using huniq0 0 0 (by simp)
    have huv0 : u = 0 ∧ v = 0 := ⟨huv0'.1.symm, huv0'.2.symm⟩
    have huvs :
        (⟨splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
            hEven⟩ : evenExteriorSubmodule (K := K) W) = u ∧
          (⟨splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
            hOdd⟩ : oddExteriorSubmodule (K := K) W) = v := by
      exact huniq0
        ⟨splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
          hEven⟩
        ⟨splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
          hOdd⟩
        hsum'
    have hAct :
        splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
          0 := by
      exact congrArg Subtype.val (huvs.2.trans huv0.2)
    simpa [oddSplitClifford_smul_def] using (Subtype.ext hAct)

/-- The chosen even and odd halves of `⋀W` are inequivalent as modules over the even split Clifford
algebra. -/
theorem not_nonempty_evenOddSplitCliffordLinearEquiv (W : Submodule K V) :
    letI := evenSplitCliffordModule (K := K) W
    letI := oddSplitCliffordModule (K := K) W
    ¬ Nonempty
      (evenExteriorSubmodule (K := K) W ≃ₗ[CliffordAlgebra.even (QuadraticForm.dualProd K W)]
        oddExteriorSubmodule (K := K) W) := by
  classical
  letI := evenSplitCliffordModule (K := K) W
  letI := oddSplitCliffordModule (K := K) W
  intro hEq
  rcases hEq with ⟨f⟩
  obtain ⟨a, haEven, haOdd⟩ := exists_evenSplitCliffordParityProjector (K := K) (W := W)
  let hone : evenExteriorSubmodule (K := K) W := ⟨1, by
    refine (mem_evenExteriorSubmodule_of_mem_exteriorPower (K := K) (W := W)
      (n := 0) (x := (1 : IsotropicExteriorModel (K := K) W))) ?_ (by simp)
    change (1 : IsotropicExteriorModel (K := K) W) ∈
      (LinearMap.range (ExteriorAlgebra.ι K : W →ₗ[K] IsotropicExteriorModel (K := K) W) ^ 0)
    simp
  ⟩
  have hone_ne : hone ≠ 0 := by
    intro h
    have h' : (hone : IsotropicExteriorModel (K := K) W) = 0 := congrArg Subtype.val h
    exact one_ne_zero h'
  have hzero : f hone = 0 := by
    calc
      f hone = f (evenSplitCliffordAction (K := K) W a hone) := by rw [haEven hone]
      _ = oddSplitCliffordAction (K := K) W a (f hone) := by
            simpa [evenSplitClifford_smul_def, oddSplitClifford_smul_def] using
              (map_smulₛₗ f a hone)
      _ = 0 := haOdd (f hone)
  have hone_eq_zero : hone = 0 := by
    exact f.injective (by simpa using hzero)
  exact hone_ne hone_eq_zero

end SplitHalfInequivalence

section SplitEvenProductClassification

variable [FiniteDimensional K V]

/-- The simultaneous even split Clifford action on the two chosen half-spin modules. -/
noncomputable def evenSplitCliffordActionProd (W : Submodule K V) :
    CliffordAlgebra.even (QuadraticForm.dualProd K W) →ₐ[K]
      Module.End K (evenExteriorSubmodule (K := K) W) ×
        Module.End K (oddExteriorSubmodule (K := K) W) :=
  (evenSplitCliffordAction (K := K) W).prod (oddSplitCliffordAction (K := K) W)

/-- A pair of endomorphisms of the chosen half-spin modules acts block-diagonally on
`⋀W = ⋀^even W ⊕ ⋀^odd W`. -/
noncomputable def splitHalfSpinBlockDiagonal (W : Submodule K V) :
    Module.End K (evenExteriorSubmodule (K := K) W) ×
      Module.End K (oddExteriorSubmodule (K := K) W) →ₐ[K]
        Module.End K (IsotropicExteriorModel (K := K) W) :=
  let e :
      (evenExteriorSubmodule (K := K) W × oddExteriorSubmodule (K := K) W) ≃ₗ[K]
        IsotropicExteriorModel (K := K) W :=
    Submodule.prodEquivOfIsCompl _ _ (evenExteriorSubmodule_isCompl (K := K) (W := W))
  (e.conjAlgEquiv K).toAlgHom.comp
    (LinearMap.prodMapAlgHom K (evenExteriorSubmodule (K := K) W)
      (oddExteriorSubmodule (K := K) W))

omit [Invertible (2 : K)] [FiniteDimensional K V] in
@[simp] theorem splitHalfSpinBlockDiagonal_apply_even (W : Submodule K V)
    (f : Module.End K (evenExteriorSubmodule (K := K) W) ×
      Module.End K (oddExteriorSubmodule (K := K) W))
    (x : evenExteriorSubmodule (K := K) W) :
    splitHalfSpinBlockDiagonal (K := K) W f x = f.1 x := by
  let e :
      (evenExteriorSubmodule (K := K) W × oddExteriorSubmodule (K := K) W) ≃ₗ[K]
        IsotropicExteriorModel (K := K) W :=
    Submodule.prodEquivOfIsCompl _ _ (evenExteriorSubmodule_isCompl (K := K) (W := W))
  simp [splitHalfSpinBlockDiagonal, LinearEquiv.conjAlgEquiv_apply]

omit [Invertible (2 : K)] [FiniteDimensional K V] in
@[simp] theorem splitHalfSpinBlockDiagonal_apply_odd (W : Submodule K V)
    (f : Module.End K (evenExteriorSubmodule (K := K) W) ×
      Module.End K (oddExteriorSubmodule (K := K) W))
    (x : oddExteriorSubmodule (K := K) W) :
    splitHalfSpinBlockDiagonal (K := K) W f x = f.2 x := by
  let e :
      (evenExteriorSubmodule (K := K) W × oddExteriorSubmodule (K := K) W) ≃ₗ[K]
        IsotropicExteriorModel (K := K) W :=
    Submodule.prodEquivOfIsCompl _ _ (evenExteriorSubmodule_isCompl (K := K) (W := W))
  simp [splitHalfSpinBlockDiagonal, LinearEquiv.conjAlgEquiv_apply]

/-- Every pair of endomorphisms of the chosen half-spin modules comes from an even split Clifford
element. -/
theorem evenSplitCliffordActionProd_surjective (W : Submodule K V) :
    Function.Surjective (evenSplitCliffordActionProd (K := K) W) := by
  classical
  let b := Module.finBasis K W
  intro f
  let p := splitHalfSpinBlockDiagonal (K := K) W f
  obtain ⟨a, ha⟩ := splitCliffordAction_surjective (K := K) (W := W) b p
  obtain ⟨aEven, aOdd, haDecomp, _⟩ := Submodule.existsUnique_add_of_isCompl
    (CliffordAlgebra.evenOdd_isCompl (Q := QuadraticForm.dualProd K W)) a
  refine ⟨aEven, Prod.ext ?_ ?_⟩
  · ext x
    have hEven :
        splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x ∈
          evenExteriorSubmodule (K := K) W :=
      splitCliffordAction_mem_evenExteriorSubmodule (K := K) (W := W) aEven.2 x.2
    have hOdd :
        splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x ∈
          oddExteriorSubmodule (K := K) W :=
      splitCliffordAction_mem_oddExteriorSubmodule_of_odd (K := K) (W := W) aOdd.2 x.2
    have hsum :
        splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
            splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
          f.1 x := by
      calc
        splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
            splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
          splitCliffordAction (K := K) W
            ((aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) +
              (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W))) x := by
              symm
              exact congrArg
                (fun g : Module.End K (IsotropicExteriorModel (K := K) W) => g x)
                ((splitCliffordAction (K := K) W).map_add
                  (aEven : CliffordAlgebra (QuadraticForm.dualProd K W))
                  (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)))
        _ = splitCliffordAction (K := K) W a x := by
              simpa using congrArg (fun z : CliffordAlgebra (QuadraticForm.dualProd K W) =>
                splitCliffordAction (K := K) W z x) haDecomp
        _ = p x := by
              simpa [p] using
                congrArg (fun g : Module.End K (IsotropicExteriorModel (K := K) W) => g x) ha
        _ = f.1 x := splitHalfSpinBlockDiagonal_apply_even (K := K) (W := W) f x
    obtain ⟨u, v, _huv, huniq⟩ := Submodule.existsUnique_add_of_isCompl
      (evenExteriorSubmodule_isCompl (K := K) (W := W)) (f.1 x : IsotropicExteriorModel (K := K) W)
    have huv0' : f.1 x = u ∧ (0 : oddExteriorSubmodule (K := K) W) = v := by
      simpa using huniq (f.1 x) 0 (by simp)
    have huv0 : u = f.1 x ∧ v = 0 := ⟨huv0'.1.symm, huv0'.2.symm⟩
    have huvs :
        (⟨splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
            hEven⟩ : evenExteriorSubmodule (K := K) W) = u ∧
          (⟨splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
            hOdd⟩ : oddExteriorSubmodule (K := K) W) = v := by
      exact huniq
        ⟨splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
          hEven⟩
        ⟨splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
          hOdd⟩
        hsum
    exact congrArg Subtype.val (huvs.1.trans huv0.1)
  · ext x
    have hOdd :
        splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x ∈
          oddExteriorSubmodule (K := K) W :=
      splitCliffordAction_mem_oddExteriorSubmodule (K := K) (W := W) aEven.2 x.2
    have hEven :
        splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x ∈
          evenExteriorSubmodule (K := K) W :=
      splitCliffordAction_mem_evenExteriorSubmodule_of_odd (K := K) (W := W) aOdd.2 x.2
    have hsum :
        splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
            splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
          f.2 x := by
      calc
        splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
            splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x =
          splitCliffordAction (K := K) W
            ((aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) +
              (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W))) x := by
              symm
              rw [show
                splitCliffordAction (K := K) W
                    ((aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) +
                      (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W))) x =
                  splitCliffordAction (K := K) W
                    (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x +
                    splitCliffordAction (K := K) W
                      (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x by
                    exact congrArg
                      (fun g : Module.End K (IsotropicExteriorModel (K := K) W) => g x)
                      ((splitCliffordAction (K := K) W).map_add
                        (aEven : CliffordAlgebra (QuadraticForm.dualProd K W))
                        (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)))]
              abel
        _ = splitCliffordAction (K := K) W a x := by
              simpa using congrArg (fun z : CliffordAlgebra (QuadraticForm.dualProd K W) =>
                splitCliffordAction (K := K) W z x) haDecomp
        _ = p x := by
              simpa [p] using
                congrArg (fun g : Module.End K (IsotropicExteriorModel (K := K) W) => g x) ha
        _ = f.2 x := splitHalfSpinBlockDiagonal_apply_odd (K := K) (W := W) f x
    obtain ⟨u, v, _huv, huniq⟩ := Submodule.existsUnique_add_of_isCompl
      (evenExteriorSubmodule_isCompl (K := K) (W := W)) (f.2 x : IsotropicExteriorModel (K := K) W)
    have huv0' : (0 : evenExteriorSubmodule (K := K) W) = u ∧ f.2 x = v := by
      simpa using huniq 0 (f.2 x) (by simp)
    have huv0 : u = 0 ∧ v = f.2 x := ⟨huv0'.1.symm, huv0'.2.symm⟩
    have huvs :
        (⟨splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
            hEven⟩ : evenExteriorSubmodule (K := K) W) = u ∧
          (⟨splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
            hOdd⟩ : oddExteriorSubmodule (K := K) W) = v := by
      exact huniq
        ⟨splitCliffordAction (K := K) W (aOdd : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
          hEven⟩
        ⟨splitCliffordAction (K := K) W (aEven : CliffordAlgebra (QuadraticForm.dualProd K W)) x,
          hOdd⟩
        hsum
    exact congrArg Subtype.val (huvs.2.trans huv0.2)

/-- The simultaneous even split Clifford action on the two chosen half-spin modules is faithful. -/
theorem evenSplitCliffordActionProd_injective (W : Submodule K V) :
    Function.Injective (evenSplitCliffordActionProd (K := K) W) := by
  classical
  let b := Module.finBasis K W
  intro a b' hab
  apply Subtype.ext
  have hEven :
      evenSplitCliffordAction (K := K) W a = evenSplitCliffordAction (K := K) W b' :=
    congrArg Prod.fst hab
  have hOdd :
      oddSplitCliffordAction (K := K) W a = oddSplitCliffordAction (K := K) W b' :=
    congrArg Prod.snd hab
  apply (splitCliffordAction_injective (K := K) (W := W) b)
  apply LinearMap.ext
  intro y
  obtain ⟨u, v, huv, _⟩ := Submodule.existsUnique_add_of_isCompl
    (evenExteriorSubmodule_isCompl (K := K) (W := W)) y
  have hu :
      splitCliffordAction (K := K) W (a : CliffordAlgebra (QuadraticForm.dualProd K W)) u =
        splitCliffordAction (K := K) W (b' : CliffordAlgebra (QuadraticForm.dualProd K W)) u := by
    exact congrArg Subtype.val (congrArg (fun g => g u) hEven)
  have hv :
      splitCliffordAction (K := K) W (a : CliffordAlgebra (QuadraticForm.dualProd K W)) v =
        splitCliffordAction (K := K) W (b' : CliffordAlgebra (QuadraticForm.dualProd K W)) v := by
    exact congrArg Subtype.val (congrArg (fun g => g v) hOdd)
  calc
    splitCliffordAction (K := K) W (a : CliffordAlgebra (QuadraticForm.dualProd K W)) y =
      splitCliffordAction (K := K) W (a : CliffordAlgebra (QuadraticForm.dualProd K W)) (u + v) := by
        rw [← huv]
    _ =
      splitCliffordAction (K := K) W (a : CliffordAlgebra (QuadraticForm.dualProd K W)) u +
        splitCliffordAction (K := K) W (a : CliffordAlgebra (QuadraticForm.dualProd K W)) v := by
          simp
    _ =
      splitCliffordAction (K := K) W (b' : CliffordAlgebra (QuadraticForm.dualProd K W)) u +
        splitCliffordAction (K := K) W (b' : CliffordAlgebra (QuadraticForm.dualProd K W)) v := by
          rw [hu, hv]
    _ =
      splitCliffordAction (K := K) W (b' : CliffordAlgebra (QuadraticForm.dualProd K W)) (u + v) := by
          simp
    _ = splitCliffordAction (K := K) W (b' : CliffordAlgebra (QuadraticForm.dualProd K W)) y := by
          rw [huv]

/-- In the finite-dimensional split case, the even Clifford algebra is identified with the product
of the endomorphism algebras of the two chosen half-spin modules. -/
noncomputable def evenSplitCliffordEquivProdEnd (W : Submodule K V) :
    CliffordAlgebra.even (QuadraticForm.dualProd K W) ≃ₐ[K]
      Module.End K (evenExteriorSubmodule (K := K) W) ×
        Module.End K (oddExteriorSubmodule (K := K) W) :=
  AlgEquiv.ofBijective (evenSplitCliffordActionProd (K := K) W)
    ⟨evenSplitCliffordActionProd_injective (K := K) (W := W),
      evenSplitCliffordActionProd_surjective (K := K) (W := W)⟩

@[simp] theorem evenSplitCliffordEquivProdEnd_apply (W : Submodule K V)
    (a : CliffordAlgebra.even (QuadraticForm.dualProd K W)) :
    evenSplitCliffordEquivProdEnd (K := K) W a =
      evenSplitCliffordActionProd (K := K) W a :=
  rfl

end SplitEvenProductClassification

/--
Restrict the split Clifford action from `Cl(W* × W, dualProd)` to the corresponding spin group.
-/
def splitSpinRepresentation (W : Submodule K V) :
    spinGroup (QuadraticForm.dualProd K W) →*
      Module.End K (IsotropicExteriorModel (K := K) W) :=
  (splitCliffordAction (K := K) W).toMonoidHom.comp (SubmonoidClass.subtype _)

instance splitMulAction (W : Submodule K V) :
    MulAction (spinGroup (QuadraticForm.dualProd K W))
      (IsotropicExteriorModel (K := K) W) :=
  MulAction.compHom (IsotropicExteriorModel (K := K) W) (splitSpinRepresentation (K := K) W)

@[simp]
theorem splitSpin_smul_def (W : Submodule K V)
    (g : spinGroup (QuadraticForm.dualProd K W))
    (x : IsotropicExteriorModel (K := K) W) :
    g • x = splitSpinRepresentation (K := K) W g x := rfl

/-- The split spin representation preserves the chosen even summand of `⋀W`. -/
theorem splitSpinRepresentation_mem_evenExteriorSubmodule (W : Submodule K V)
    {g : spinGroup (QuadraticForm.dualProd K W)}
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ evenExteriorSubmodule (K := K) W) :
    splitSpinRepresentation (K := K) W g x ∈ evenExteriorSubmodule (K := K) W := by
  simpa [splitSpinRepresentation] using
    splitCliffordAction_mem_evenExteriorSubmodule (K := K) (W := W)
      (a := (g : CliffordAlgebra (QuadraticForm.dualProd K W))) (spinGroup.mem_even g.property) hx

/-- The split spin representation preserves the chosen odd summand of `⋀W`. -/
theorem splitSpinRepresentation_mem_oddExteriorSubmodule (W : Submodule K V)
    {g : spinGroup (QuadraticForm.dualProd K W)}
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ oddExteriorSubmodule (K := K) W) :
    splitSpinRepresentation (K := K) W g x ∈ oddExteriorSubmodule (K := K) W := by
  simpa [splitSpinRepresentation] using
    splitCliffordAction_mem_oddExteriorSubmodule (K := K) (W := W)
      (a := (g : CliffordAlgebra (QuadraticForm.dualProd K W))) (spinGroup.mem_even g.property) hx

/-- The split spin representation restricted to the chosen even summand. -/
noncomputable def evenSplitSpinRepresentation (W : Submodule K V) :
    spinGroup (QuadraticForm.dualProd K W) →*
      Module.End K (evenExteriorSubmodule (K := K) W) where
  toFun g :=
    LinearMap.restrict (splitSpinRepresentation (K := K) W g)
      (fun x hx => splitSpinRepresentation_mem_evenExteriorSubmodule (K := K) (W := W) hx)
  map_one' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    ext x
    simp [LinearMap.restrict_apply]

/-- The split spin representation restricted to the chosen odd summand. -/
noncomputable def oddSplitSpinRepresentation (W : Submodule K V) :
    spinGroup (QuadraticForm.dualProd K W) →*
      Module.End K (oddExteriorSubmodule (K := K) W) where
  toFun g :=
    LinearMap.restrict (splitSpinRepresentation (K := K) W g)
      (fun x hx => splitSpinRepresentation_mem_oddExteriorSubmodule (K := K) (W := W) hx)
  map_one' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    ext x
    simp [LinearMap.restrict_apply]

noncomputable instance (W : Submodule K V) :
    MulAction (spinGroup (QuadraticForm.dualProd K W))
      (evenExteriorSubmodule (K := K) W) :=
  MulAction.compHom (evenExteriorSubmodule (K := K) W) (evenSplitSpinRepresentation (K := K) W)

noncomputable instance (W : Submodule K V) :
    MulAction (spinGroup (QuadraticForm.dualProd K W))
      (oddExteriorSubmodule (K := K) W) :=
  MulAction.compHom (oddExteriorSubmodule (K := K) W) (oddSplitSpinRepresentation (K := K) W)

@[simp]
theorem evenSplitSpin_smul_def (W : Submodule K V)
    (g : spinGroup (QuadraticForm.dualProd K W))
    (x : evenExteriorSubmodule (K := K) W) :
    g • x = evenSplitSpinRepresentation (K := K) W g x := rfl

@[simp]
theorem oddSplitSpin_smul_def (W : Submodule K V)
    (g : spinGroup (QuadraticForm.dualProd K W))
    (x : oddExteriorSubmodule (K := K) W) :
    g • x = oddSplitSpinRepresentation (K := K) W g x := rfl

end Contraction

end ChosenSubspaceModel

section WittModel

variable [FiniteDimensional K V]

/-- The canonical `⋀W` model built from the chosen Witt subspace of `Q`. -/
abbrev WittExteriorModel (Q : QuadraticForm K V) := IsotropicExteriorModel (K := K) Q.wittSubspace

/-- The even-degree half of the chosen Witt model. -/
noncomputable abbrev evenWittExterior (Q : QuadraticForm K V) :=
  evenExteriorSubmodule (K := K) Q.wittSubspace

/-- The odd-degree half of the chosen Witt model. -/
noncomputable abbrev oddWittExterior (Q : QuadraticForm K V) :=
  oddExteriorSubmodule (K := K) Q.wittSubspace

section SplitParity

variable [Invertible (2 : K)]

/-- The split spin action on the canonical Witt model `⋀(Q.wittSubspace)`. -/
noncomputable abbrev wittSplitSpinRepresentation (Q : QuadraticForm K V) :=
  splitSpinRepresentation (K := K) Q.wittSubspace

/-- The split spin action restricted to the even half of the canonical Witt model. -/
noncomputable abbrev evenWittSplitSpinRepresentation (Q : QuadraticForm K V) :=
  evenSplitSpinRepresentation (K := K) Q.wittSubspace

/-- The split spin action restricted to the odd half of the canonical Witt model. -/
noncomputable abbrev oddWittSplitSpinRepresentation (Q : QuadraticForm K V) :=
  oddSplitSpinRepresentation (K := K) Q.wittSubspace

end SplitParity

theorem finrank_isotropicExteriorModel (W : Submodule K V) :
    Module.finrank K (IsotropicExteriorModel (K := K) W) = 2 ^ Module.finrank K W := by
  simpa [IsotropicExteriorModel] using (ExteriorAlgebra.finrank_eq_two_pow (K := K) (M := W))

theorem finrank_wittExteriorModel (Q : QuadraticForm K V) :
    Module.finrank K (WittExteriorModel (K := K) Q) = 2 ^ Q.wittIndex := by
  rw [finrank_isotropicExteriorModel, Q.finrank_wittSubspace]

theorem evenWittExterior_isCompl (Q : QuadraticForm K V) :
    IsCompl (evenWittExterior (K := K) Q) (oddWittExterior (K := K) Q) :=
  evenExteriorSubmodule_isCompl (K := K) (W := Q.wittSubspace)

theorem evenWittExterior_sup_oddWittExterior (Q : QuadraticForm K V) :
    evenWittExterior (K := K) Q ⊔ oddWittExterior (K := K) Q = ⊤ :=
  (evenWittExterior_isCompl (K := K) Q).sup_eq_top

theorem evenWittExterior_inf_oddWittExterior (Q : QuadraticForm K V) :
    evenWittExterior (K := K) Q ⊓ oddWittExterior (K := K) Q = ⊥ :=
  (evenWittExterior_isCompl (K := K) Q).inf_eq_bot

section SplitParity

variable [Invertible (2 : K)]

theorem wittSplitSpinRepresentation_mem_evenWittExterior (Q : QuadraticForm K V)
    {g : spinGroup (QuadraticForm.dualProd K Q.wittSubspace)}
    {x : WittExteriorModel (K := K) Q} (hx : x ∈ evenWittExterior (K := K) Q) :
    wittSplitSpinRepresentation (K := K) Q g x ∈ evenWittExterior (K := K) Q := by
  exact splitSpinRepresentation_mem_evenExteriorSubmodule (K := K) (W := Q.wittSubspace) hx

theorem wittSplitSpinRepresentation_mem_oddWittExterior (Q : QuadraticForm K V)
    {g : spinGroup (QuadraticForm.dualProd K Q.wittSubspace)}
    {x : WittExteriorModel (K := K) Q} (hx : x ∈ oddWittExterior (K := K) Q) :
    wittSplitSpinRepresentation (K := K) Q g x ∈ oddWittExterior (K := K) Q := by
  exact splitSpinRepresentation_mem_oddExteriorSubmodule (K := K) (W := Q.wittSubspace) hx

end SplitParity

end WittModel

end Spinor
