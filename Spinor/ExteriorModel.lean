/-
  Exterior-algebra models attached to chosen isotropic subspaces.
-/

import Spinor.Basic

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
