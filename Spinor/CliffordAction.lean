/-
  Clifford action on the exterior-model spinor module.
-/

import Spinor.Basic

/-!
# Ambient Clifford action on the exterior spinor module

Transport of the left regular action of `CliffordAlgebra Q` on itself to the ambient
exterior-algebra spinor module `SpinorModule Q := ExteriorAlgebra R M`, via the Mathlib
linear equivalence `CliffordAlgebra.equivExterior`. This gives `SpinorModule Q` its
first-class `Module (CliffordAlgebra Q)` structure and a faithful vector relation; the
`spinGroup Q` action is then derived by restriction in `Spinor.SpinRep`.

## Main declarations

* `Spinor.cliffordAction Q` — the transported algebra homomorphism
  `CliffordAlgebra Q →ₐ[R] Module.End R (SpinorModule Q)`.
* `Spinor.cliffordAction_ι_sq` — the Clifford vector relation `ι(m) · ι(m) = Q m`.
* `Spinor.cliffordAction_injective` — faithfulness in characteristic not two (via
  `Invertible (2 : R)`).
* The `Module (CliffordAlgebra Q) (SpinorModule Q)` instance and the
  `Spinor.clifford_smul_def` unfolding lemma.
-/

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
