/-
  Chiral decomposition for the exterior-model spinor module.
-/

import Spinor.ExteriorModel
import Spinor.SpinRep

namespace Spinor

universe uR uM

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [Invertible (2 : R)]

/--
The `i`-chiral piece of the exterior-model spinor module, transported from the
`ZMod 2`-grading on `CliffordAlgebra Q`.
-/
def chiralSubmodule (i : ZMod 2) : Submodule R (SpinorModule (R := R) (M := M) Q) :=
  Submodule.comap (CliffordAlgebra.equivExterior Q).symm.toLinearMap (CliffordAlgebra.evenOdd Q i)

/-- Positive-chirality spinors. -/
abbrev positiveChiral : Submodule R (SpinorModule (R := R) (M := M) Q) :=
  chiralSubmodule (R := R) (M := M) Q 0

/-- Negative-chirality spinors. -/
abbrev negativeChiral : Submodule R (SpinorModule (R := R) (M := M) Q) :=
  chiralSubmodule (R := R) (M := M) Q 1

@[simp]
theorem mem_chiralSubmodule_iff {i : ZMod 2} {x : SpinorModule (R := R) (M := M) Q} :
    x ∈ chiralSubmodule (R := R) (M := M) Q i ↔
      (CliffordAlgebra.equivExterior Q).symm x ∈ CliffordAlgebra.evenOdd Q i := by
  rfl

@[simp]
theorem mem_positiveChiral_iff {x : SpinorModule (R := R) (M := M) Q} :
    x ∈ positiveChiral (R := R) (M := M) Q ↔
      (CliffordAlgebra.equivExterior Q).symm x ∈ CliffordAlgebra.evenOdd Q 0 := by
  rfl

@[simp]
theorem mem_negativeChiral_iff {x : SpinorModule (R := R) (M := M) Q} :
    x ∈ negativeChiral (R := R) (M := M) Q ↔
      (CliffordAlgebra.equivExterior Q).symm x ∈ CliffordAlgebra.evenOdd Q 1 := by
  rfl

theorem chiralSubmodule_eq_map (i : ZMod 2) :
    chiralSubmodule (R := R) (M := M) Q i =
      (CliffordAlgebra.evenOdd Q i).map (CliffordAlgebra.equivExterior Q).toLinearMap := by
  ext x
  rw [chiralSubmodule, Submodule.map_equiv_eq_comap_symm]

theorem chiralSubmodule_isCompl :
    IsCompl (positiveChiral (R := R) (M := M) Q) (negativeChiral (R := R) (M := M) Q) := by
  have h :
      IsCompl
        ((Submodule.orderIsoMapComap (CliffordAlgebra.equivExterior Q)) (CliffordAlgebra.evenOdd Q 0))
        ((Submodule.orderIsoMapComap (CliffordAlgebra.equivExterior Q)) (CliffordAlgebra.evenOdd Q 1)) :=
    (OrderIso.isCompl_iff (Submodule.orderIsoMapComap (CliffordAlgebra.equivExterior Q))
      (x := CliffordAlgebra.evenOdd Q 0) (y := CliffordAlgebra.evenOdd Q 1)).1
      (CliffordAlgebra.evenOdd_isCompl (Q := Q))
  simpa [positiveChiral, negativeChiral, chiralSubmodule_eq_map] using h

theorem positiveChiral_sup_negativeChiral :
    positiveChiral (R := R) (M := M) Q ⊔ negativeChiral (R := R) (M := M) Q = ⊤ :=
  (chiralSubmodule_isCompl (R := R) (M := M) Q).sup_eq_top

theorem positiveChiral_inf_negativeChiral :
    positiveChiral (R := R) (M := M) Q ⊓ negativeChiral (R := R) (M := M) Q = ⊥ :=
  (chiralSubmodule_isCompl (R := R) (M := M) Q).inf_eq_bot

section ZeroFormChosenModel

variable {K : Type uR} [Field K]
variable {V : Type uM} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (W : Submodule K V)

private theorem exteriorPower_le_zero_evenOdd_zero_of_even {n : ℕ} (hn : Even n) :
    (⋀[K]^n W : Submodule K (IsotropicExteriorModel (K := K) W)) ≤
      CliffordAlgebra.evenOdd (0 : QuadraticForm K W) 0 := by
  obtain ⟨m, rfl⟩ := hn
  intro x hx
  have hx' :
      x ∈ (LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm K W))) ^ (m + m) := by
    simpa [ExteriorAlgebra.exteriorPower] using hx
  have hz : (((m + m : ℕ) : ZMod 2)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact ⟨m, by omega⟩
  exact Submodule.mem_iSup_of_mem ⟨m + m, hz⟩ hx'

private theorem exteriorPower_le_zero_evenOdd_one_of_odd {n : ℕ} (hn : ¬ Even n) :
    (⋀[K]^n W : Submodule K (IsotropicExteriorModel (K := K) W)) ≤
      CliffordAlgebra.evenOdd (0 : QuadraticForm K W) 1 := by
  obtain ⟨m, rfl⟩ := Nat.not_even_iff_odd.mp hn
  intro x hx
  have hx' :
      x ∈ (LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm K W))) ^ (2 * m + 1) := by
    simpa [ExteriorAlgebra.exteriorPower] using hx
  have hz : (((2 * m + 1 : ℕ) : ZMod 2)) = 1 := by
    have hz' : (((2 * m + 1 : ℕ) : ZMod 2)) = (((1 : ℕ) : ZMod 2)) := by
      rw [ZMod.natCast_eq_natCast_iff']
      simp
    simpa using hz'
  exact Submodule.mem_iSup_of_mem ⟨2 * m + 1, hz⟩ hx'

private theorem zero_evenOdd_zero_le_evenExteriorSubmodule :
    CliffordAlgebra.evenOdd (0 : QuadraticForm K W) 0 ≤ evenExteriorSubmodule (K := K) W := by
  intro x hx
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
      exact mem_evenExteriorSubmodule_of_mem_exteriorPower (K := K) (W := W)
        (by simpa [pow_zero] : algebraMap K (IsotropicExteriorModel (K := K) W) r ∈ ⋀[K]^0 W)
        (by simp)
  | add x y hx hy ihx ihy =>
      exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
      have hodd : (ExteriorAlgebra.ι K m₂) * x ∈ oddExteriorSubmodule (K := K) W := by
        simpa [wedgeAction_apply] using
          wedgeAction_mem_oddExteriorSubmodule (K := K) (W := W) m₂ ih
      have heven :
          (ExteriorAlgebra.ι K m₁) * ((ExteriorAlgebra.ι K m₂) * x) ∈
            evenExteriorSubmodule (K := K) W := by
        simpa [wedgeAction_apply] using
          wedgeAction_mem_evenExteriorSubmodule (K := K) (W := W) m₁ hodd
      simpa [mul_assoc] using heven

private theorem evenExteriorSubmodule_le_zero_evenOdd_zero :
    evenExteriorSubmodule (K := K) W ≤ CliffordAlgebra.evenOdd (0 : QuadraticForm K W) 0 := by
  classical
  intro x hx
  have hxsum :
      x = Finset.sum (exteriorDecompose (K := K) W x).support
        (fun i =>
          (((exteriorDecompose (K := K) W x) i : ⋀[K]^i W) :
            IsotropicExteriorModel (K := K) W)) := by
    simpa using (DirectSum.sum_support_decompose (fun i : ℕ => ⋀[K]^i W) x).symm
  rw [hxsum]
  refine Submodule.sum_mem _ ?_
  intro i hi
  have hne : exteriorDecompose (K := K) W x i ≠ 0 := DFinsupp.mem_support_iff.mp hi
  have hi_even : Even i := by
    by_contra hodd
    exact hne (hx i hodd)
  exact exteriorPower_le_zero_evenOdd_zero_of_even (K := K) (W := W) hi_even
    (show ((((exteriorDecompose (K := K) W x) i : ⋀[K]^i W) :
        IsotropicExteriorModel (K := K) W)) ∈ ⋀[K]^i W from
      (exteriorDecompose (K := K) W x i).property)

/--
For the zero quadratic form on the chosen isotropic space `W`, the abstract even Clifford parity
piece is exactly the explicit even-degree exterior summand `⋀^even W`.
-/
theorem zero_evenOdd_zero_eq_evenExteriorSubmodule :
    CliffordAlgebra.evenOdd (0 : QuadraticForm K W) 0 =
      evenExteriorSubmodule (K := K) W := by
  exact le_antisymm
    (zero_evenOdd_zero_le_evenExteriorSubmodule (K := K) (W := W))
    (evenExteriorSubmodule_le_zero_evenOdd_zero (K := K) (W := W))

private theorem zero_evenOdd_one_le_oddExteriorSubmodule :
    CliffordAlgebra.evenOdd (0 : QuadraticForm K W) 1 ≤ oddExteriorSubmodule (K := K) W := by
  intro x hx
  induction x, hx using CliffordAlgebra.odd_induction with
  | ι m =>
      exact mem_oddExteriorSubmodule_of_mem_exteriorPower (K := K) (W := W)
        (n := 1) (x := ExteriorAlgebra.ι K m)
        (by simpa [pow_one] using LinearMap.mem_range_self (ExteriorAlgebra.ι K) m)
        (by simp)
  | add x y hx hy ihx ihy =>
      exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
      have heven : (ExteriorAlgebra.ι K m₂) * x ∈ evenExteriorSubmodule (K := K) W := by
        simpa [wedgeAction_apply] using
          wedgeAction_mem_evenExteriorSubmodule (K := K) (W := W) m₂ ih
      have hodd :
          (ExteriorAlgebra.ι K m₁) * ((ExteriorAlgebra.ι K m₂) * x) ∈
            oddExteriorSubmodule (K := K) W := by
        simpa [wedgeAction_apply] using
          wedgeAction_mem_oddExteriorSubmodule (K := K) (W := W) m₁ heven
      simpa [mul_assoc] using hodd

private theorem oddExteriorSubmodule_le_zero_evenOdd_one :
    oddExteriorSubmodule (K := K) W ≤ CliffordAlgebra.evenOdd (0 : QuadraticForm K W) 1 := by
  classical
  intro x hx
  have hxsum :
      x = Finset.sum (exteriorDecompose (K := K) W x).support
        (fun i =>
          (((exteriorDecompose (K := K) W x) i : ⋀[K]^i W) :
            IsotropicExteriorModel (K := K) W)) := by
    simpa using (DirectSum.sum_support_decompose (fun i : ℕ => ⋀[K]^i W) x).symm
  rw [hxsum]
  refine Submodule.sum_mem _ ?_
  intro i hi
  have hne : exteriorDecompose (K := K) W x i ≠ 0 := DFinsupp.mem_support_iff.mp hi
  have hi_odd : ¬ Even i := by
    intro hi_even
    exact hne (hx i hi_even)
  exact exteriorPower_le_zero_evenOdd_one_of_odd (K := K) (W := W) hi_odd
    (show ((((exteriorDecompose (K := K) W x) i : ⋀[K]^i W) :
        IsotropicExteriorModel (K := K) W)) ∈ ⋀[K]^i W from
      (exteriorDecompose (K := K) W x i).property)

/--
For the zero quadratic form on the chosen isotropic space `W`, the abstract odd Clifford parity
piece is exactly the explicit odd-degree exterior summand `⋀^odd W`.
-/
theorem zero_evenOdd_one_eq_oddExteriorSubmodule :
    CliffordAlgebra.evenOdd (0 : QuadraticForm K W) 1 =
      oddExteriorSubmodule (K := K) W := by
  exact le_antisymm
    (zero_evenOdd_one_le_oddExteriorSubmodule (K := K) (W := W))
    (oddExteriorSubmodule_le_zero_evenOdd_one (K := K) (W := W))

variable [Invertible (2 : K)]

@[simp]
theorem equivExterior_zero :
    CliffordAlgebra.equivExterior (0 : QuadraticForm K W) = LinearEquiv.refl K _ := by
  ext x <;>
    simp [CliffordAlgebra.equivExterior, CliffordAlgebra.changeForm.associated_neg_proof,
      CliffordAlgebra.changeFormEquiv]

@[simp]
theorem equivExterior_zero_symm :
    (CliffordAlgebra.equivExterior (0 : QuadraticForm K W)).symm = LinearEquiv.refl K _ := by
  simpa using congrArg LinearEquiv.symm (equivExterior_zero (K := K) (W := W))

@[simp]
theorem equivExterior_zero_symm_apply (x : SpinorModule (R := K) (M := W) (0 : QuadraticForm K W)) :
    (CliffordAlgebra.equivExterior (0 : QuadraticForm K W)).symm x = x := by
  simpa using congrArg (fun e => e x) (equivExterior_zero_symm (K := K) (W := W))

/--
On the zero-form chosen model `⋀W`, the transported positive-chiral submodule is the explicit
even-degree summand `⋀^even W`.
-/
theorem positiveChiral_zero_eq_evenExteriorSubmodule :
    positiveChiral (R := K) (M := W) (0 : QuadraticForm K W) =
      evenExteriorSubmodule (K := K) W := by
  ext x
  rw [mem_positiveChiral_iff, equivExterior_zero_symm_apply (K := K) (W := W) x]
  rw [zero_evenOdd_zero_eq_evenExteriorSubmodule (K := K) (W := W)]

/--
On the zero-form chosen model `⋀W`, the transported negative-chiral submodule is the explicit
odd-degree summand `⋀^odd W`.
-/
theorem negativeChiral_zero_eq_oddExteriorSubmodule :
    negativeChiral (R := K) (M := W) (0 : QuadraticForm K W) =
      oddExteriorSubmodule (K := K) W := by
  ext x
  rw [mem_negativeChiral_iff, equivExterior_zero_symm_apply (K := K) (W := W) x]
  rw [zero_evenOdd_one_eq_oddExteriorSubmodule (K := K) (W := W)]

end ZeroFormChosenModel

@[simp]
theorem cliffordAction_symm_apply (a : CliffordAlgebra Q) (v : SpinorModule (R := R) (M := M) Q) :
    (CliffordAlgebra.equivExterior Q).symm (cliffordAction Q a v) =
      a * (CliffordAlgebra.equivExterior Q).symm v := by
  rw [cliffordAction_apply]
  exact (CliffordAlgebra.equivExterior Q).left_inv _

theorem cliffordAction_symm_mem_evenOdd {a : CliffordAlgebra Q} (ha : a ∈ CliffordAlgebra.evenOdd Q 0)
    {i : ZMod 2} {v : SpinorModule (R := R) (M := M) Q}
    (hv : (CliffordAlgebra.equivExterior Q).symm v ∈ CliffordAlgebra.evenOdd Q i) :
    (CliffordAlgebra.equivExterior Q).symm (cliffordAction Q a v) ∈ CliffordAlgebra.evenOdd Q i := by
  have hv' :
      (CliffordAlgebra.changeForm
        (CliffordAlgebra.changeForm.neg_proof CliffordAlgebra.changeForm.associated_neg_proof)) v ∈
        CliffordAlgebra.evenOdd Q i := by
    simpa [CliffordAlgebra.equivExterior] using hv
  have hm :
      a *
          (CliffordAlgebra.changeForm
            (CliffordAlgebra.changeForm.neg_proof CliffordAlgebra.changeForm.associated_neg_proof)) v ∈
        CliffordAlgebra.evenOdd Q (0 + i) :=
    SetLike.mul_mem_graded (A := CliffordAlgebra.evenOdd Q) ha hv'
  rw [cliffordAction_symm_apply (Q := Q)]
  simpa [CliffordAlgebra.equivExterior] using hm

theorem cliffordAction_mem_chiralSubmodule {a : CliffordAlgebra Q} (ha : a ∈ CliffordAlgebra.evenOdd Q 0)
    {i : ZMod 2} {v : SpinorModule (R := R) (M := M) Q}
    (hv : v ∈ chiralSubmodule (R := R) (M := M) Q i) :
    cliffordAction Q a v ∈ chiralSubmodule (R := R) (M := M) Q i := by
  change (CliffordAlgebra.equivExterior Q).symm (cliffordAction Q a v) ∈ CliffordAlgebra.evenOdd Q i
  exact cliffordAction_symm_mem_evenOdd (Q := Q) ha hv

theorem spinRepresentation_mem_chiralSubmodule {x : spinGroup Q} {i : ZMod 2}
    {v : SpinorModule (R := R) (M := M) Q}
    (hv : v ∈ chiralSubmodule (R := R) (M := M) Q i) :
    spinRepresentation Q x v ∈ chiralSubmodule (R := R) (M := M) Q i := by
  simpa [spinRepresentation_apply] using
    cliffordAction_mem_chiralSubmodule
      (Q := Q) (a := x) (spinGroup.mem_even x.property) hv

theorem spinRepresentation_mem_positiveChiral {x : spinGroup Q}
    {v : SpinorModule (R := R) (M := M) Q}
    (hv : v ∈ positiveChiral (R := R) (M := M) Q) :
    spinRepresentation Q x v ∈ positiveChiral (R := R) (M := M) Q := by
  exact spinRepresentation_mem_chiralSubmodule (Q := Q) (i := 0) hv

theorem spinRepresentation_mem_negativeChiral {x : spinGroup Q}
    {v : SpinorModule (R := R) (M := M) Q}
    (hv : v ∈ negativeChiral (R := R) (M := M) Q) :
    spinRepresentation Q x v ∈ negativeChiral (R := R) (M := M) Q := by
  exact spinRepresentation_mem_chiralSubmodule (Q := Q) (i := 1) hv

/-- The spin representation restricted to a single chiral summand. -/
def spinRepresentationOnChiral (i : ZMod 2) :
    spinGroup Q →* Module.End R (chiralSubmodule (R := R) (M := M) Q i) where
  toFun x :=
    LinearMap.restrict (spinRepresentation Q x)
      (fun v hv => spinRepresentation_mem_chiralSubmodule (Q := Q) (x := x) (i := i) hv)
  map_one' := by
    ext v
    simp [LinearMap.restrict_apply]
  map_mul' x y := by
    ext v
    simp [LinearMap.restrict_apply]

/-- The positive-chirality spin representation. -/
abbrev positiveSpinRepresentation :
    spinGroup Q →* Module.End R (positiveChiral (R := R) (M := M) Q) :=
  spinRepresentationOnChiral (R := R) (M := M) Q 0

/-- The negative-chirality spin representation. -/
abbrev negativeSpinRepresentation :
    spinGroup Q →* Module.End R (negativeChiral (R := R) (M := M) Q) :=
  spinRepresentationOnChiral (R := R) (M := M) Q 1

end Spinor
