/-
  Chiral decomposition for the exterior-model spinor module.
-/

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
