/-
  Spin-group representation induced from the transported Clifford action.
-/

import Spinor.CliffordAction

namespace Spinor

universe uR uM

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- Restrict the transported Clifford action from `CliffordAlgebra Q` to `spinGroup Q`. -/
def spinRepresentation : spinGroup Q →* Module.End R (SpinorModule (R := R) (M := M) Q) :=
  (cliffordAction Q).toRingHom.toMonoidHom.comp (SubmonoidClass.subtype (spinGroup Q))

theorem spinRepresentation_injective : Function.Injective (spinRepresentation Q) := by
  intro x y h
  apply Subtype.ext
  apply cliffordAction_injective (Q := Q)
  exact h

instance : MulAction (spinGroup Q) (SpinorModule (R := R) (M := M) Q) :=
  MulAction.compHom (SpinorModule (R := R) (M := M) Q) (spinRepresentation Q)

@[simp]
theorem spin_smul_def (x : spinGroup Q) (v : SpinorModule (R := R) (M := M) Q) :
    x • v = spinRepresentation Q x v := rfl

instance : FaithfulSMul (spinGroup Q) (SpinorModule (R := R) (M := M) Q) where
  eq_of_smul_eq_smul := by
    intro x y hxy
    apply spinRepresentation_injective (Q := Q)
    apply LinearMap.ext
    intro v
    exact hxy v

@[simp]
theorem spinRepresentation_apply (x : spinGroup Q) :
    spinRepresentation Q x = cliffordAction Q x := rfl

end Spinor
