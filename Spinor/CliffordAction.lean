/-
  Clifford action on the exterior-model spinor module.
-/

import Spinor.Basic

namespace Spinor

universe uR uM

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [Invertible (2 : R)]

/--
Transport the left regular action of `CliffordAlgebra Q` to `SpinorModule Q`
using `CliffordAlgebra.equivExterior`.
-/
def cliffordAction : CliffordAlgebra Q →ₐ[R] Module.End R (SpinorModule (R := R) (M := M) Q) :=
  (LinearEquiv.conjAlgEquiv R (CliffordAlgebra.equivExterior Q)).toAlgHom.comp
    (Algebra.lmul R (CliffordAlgebra Q))

@[simp]
theorem cliffordAction_apply (a : CliffordAlgebra Q) (x : SpinorModule (R := R) (M := M) Q) :
    cliffordAction Q a x =
      CliffordAlgebra.equivExterior Q (a * (CliffordAlgebra.equivExterior Q).symm x) := by
  simp [cliffordAction]

@[simp]
theorem cliffordAction_ι_sq (m : M) :
    cliffordAction Q (CliffordAlgebra.ι Q m) * cliffordAction Q (CliffordAlgebra.ι Q m) =
      algebraMap R (Module.End R (SpinorModule (R := R) (M := M) Q)) (Q m) := by
  rw [← map_mul, CliffordAlgebra.ι_sq_scalar, AlgHom.commutes]

theorem cliffordAction_injective : Function.Injective (cliffordAction Q) := by
  intro a b h
  apply (CliffordAlgebra.equivExterior Q).injective
  have hEval :=
    congrArg
      (fun f : Module.End R (SpinorModule (R := R) (M := M) Q) =>
        f (CliffordAlgebra.equivExterior Q 1))
      h
  simpa [cliffordAction] using hEval

instance : Module (CliffordAlgebra Q) (SpinorModule (R := R) (M := M) Q) :=
  Module.compHom (SpinorModule (R := R) (M := M) Q) (cliffordAction Q).toRingHom

@[simp]
theorem clifford_smul_def (a : CliffordAlgebra Q) (x : SpinorModule (R := R) (M := M) Q) :
    a • x = cliffordAction Q a x := rfl

instance : FaithfulSMul (CliffordAlgebra Q) (SpinorModule (R := R) (M := M) Q) where
  eq_of_smul_eq_smul := by
    intro a b hab
    apply cliffordAction_injective (Q := Q)
    apply LinearMap.ext
    intro x
    exact hab x

end Spinor
