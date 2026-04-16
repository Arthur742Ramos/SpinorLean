/-
  Spin-group representation induced from the transported Clifford action.
-/

import Spinor.CliffordAction

/-!
# Ambient spin-group representation on the exterior spinor module

Restriction of the ambient Clifford action from `Spinor.CliffordAction` to the subgroup
`spinGroup Q`, giving the ambient spin representation on `SpinorModule Q`.

The resulting homomorphism is injective whenever `Invertible (2 : R)`, and scalar elements
of `spinGroup Q` act as the matching scalar endomorphisms. Non-factorization criteria and
kernel identifications built on top of this representation live in `Spinor.OrthogonalAction`
and `Spinor.Presentation`.

## Main declarations

* `Spinor.spinRepresentation Q` — the restricted homomorphism
  `spinGroup Q →* Module.End R (SpinorModule Q)`.
* `Spinor.spinRepresentation_injective`, `Spinor.spinRepresentation_eq_one_iff` —
  faithfulness of the ambient spin representation.
* `Spinor.spinRepresentation_eq_algebraMap_of_coe_eq_algebraMap`,
  `Spinor.spinRepresentation_apply_of_coe_eq_algebraMap` — scalar spin elements act as the
  matching scalar endomorphism.
* `Spinor.spinRepresentation_ne_one_of_coe_eq_algebraMap_of_ne_one` — a nontrivial scalar
  spin element acts nontrivially.
* The `MulAction (spinGroup Q) (SpinorModule Q)` and `FaithfulSMul` instances and the
  `Spinor.spin_smul_def` unfolding lemma.
-/

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

/-- If a spin element is a scalar in the Clifford algebra, then its spinor action is the matching
scalar endomorphism. -/
theorem spinRepresentation_eq_algebraMap_of_coe_eq_algebraMap (x : spinGroup Q) (r : R)
    (hx : (x : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) r) :
    spinRepresentation Q x =
      algebraMap R (Module.End R (SpinorModule (R := R) (M := M) Q)) r := by
  rw [spinRepresentation_apply, hx]
  exact (cliffordAction Q).commutes r

/-- Pointwise form of `spinRepresentation_eq_algebraMap_of_coe_eq_algebraMap`. -/
theorem spinRepresentation_apply_of_coe_eq_algebraMap (x : spinGroup Q) (r : R)
    (hx : (x : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) r)
    (v : SpinorModule (R := R) (M := M) Q) :
    spinRepresentation Q x v = r • v := by
  simpa [Algebra.smul_def] using
    congrArg (fun f : Module.End R (SpinorModule (R := R) (M := M) Q) => f v)
      (spinRepresentation_eq_algebraMap_of_coe_eq_algebraMap (Q := Q) x r hx)

@[simp]
theorem spinRepresentation_eq_one_iff (x : spinGroup Q) :
    spinRepresentation Q x = 1 ↔ x = 1 := by
  constructor
  · intro hx
    exact spinRepresentation_injective (Q := Q) (by simpa using hx)
  · intro hx
    rw [hx]
    simp

/-- A nontrivial scalar spin element acts nontrivially in the spin representation. -/
theorem spinRepresentation_ne_one_of_coe_eq_algebraMap_of_ne_one (x : spinGroup Q) (r : R)
    (hx : (x : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) r) (hr : r ≠ 1) :
    spinRepresentation Q x ≠ 1 := by
  intro hspin
  have hAlgInj : Function.Injective (algebraMap R (CliffordAlgebra Q)) := by
    intro a b hab
    have hab' : algebraMap R (ExteriorAlgebra R M) a = algebraMap R (ExteriorAlgebra R M) b := by
      simpa [CliffordAlgebra.equivExterior] using congrArg (CliffordAlgebra.equivExterior Q) hab
    exact (ExteriorAlgebra.algebraMap_leftInverse (R := R) M).injective hab'
  apply hr
  apply hAlgInj
  calc
    algebraMap R (CliffordAlgebra Q) r = (x : CliffordAlgebra Q) := hx.symm
    _ = ((1 : spinGroup Q) : CliffordAlgebra Q) := by
      exact congrArg (fun y : spinGroup Q => (y : CliffordAlgebra Q))
        ((spinRepresentation_eq_one_iff (Q := Q) x).mp hspin)
    _ = algebraMap R (CliffordAlgebra Q) 1 := rfl

end Spinor
