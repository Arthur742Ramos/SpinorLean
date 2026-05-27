/-
  Noncanonical spinor-norm wrappers on the Lipschitz linear image.
-/

import Spinor.CliffordNorm
import Spinor.OrthogonalAction

/-!
# Lipschitz image spinor-norm wrappers

This module packages the Clifford/Lipschitz norm substrate at the image of the
ambient Lipschitz linear representation. The definitions here are deliberately
noncanonical: an image element is evaluated by choosing a Lipschitz lift and then
using the chosen-factorization API from `Spinor.CliffordNorm`.

No independence from either the chosen lift or the chosen vector factorization is
asserted here. The point is to expose a precise theorem-facing API at the
Lipschitz-image level without claiming a descended orthogonal-group spinor norm.

## Main declarations

* `Spinor.lipschitzLinearImage`
* `Spinor.lipschitzLinearImageChosenLift`
* `Spinor.lipschitzLinearImageChosenNormUnit`
* `Spinor.lipschitzLinearImageChosenSpinorNormClass`
-/

namespace Spinor

universe uR uM

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- The image subgroup of the ambient Lipschitz linear representation. -/
noncomputable abbrev lipschitzLinearImage [Invertible (2 : R)] (Q : QuadraticForm R M) :=
  MonoidHom.range (lipschitzLinearRepresentation (Q := Q))

/-- A noncomputable chosen Lipschitz lift of an element in the Lipschitz linear image. -/
noncomputable def lipschitzLinearImageChosenLift [Invertible (2 : R)]
    (Q : QuadraticForm R M) (g : lipschitzLinearImage Q) : lipschitzGroup Q :=
  Classical.choose g.property

/-- The chosen lift maps to the Lipschitz linear-image element it was chosen for. -/
theorem lipschitzLinearImageChosenLift_spec [Invertible (2 : R)]
    (Q : QuadraticForm R M) (g : lipschitzLinearImage Q) :
    lipschitzLinearRepresentation (Q := Q) (lipschitzLinearImageChosenLift Q g) = g :=
  Classical.choose_spec g.property

/-- The Clifford norm unit attached to the chosen Lipschitz lift of a linear-image element. -/
noncomputable def lipschitzLinearImageChosenNormUnit [Invertible (2 : R)]
    (Q : QuadraticForm R M) (g : lipschitzLinearImage Q) : Rˣ :=
  chosenLipschitzNormUnit Q (lipschitzLinearImageChosenLift Q g)

/--
The square-class attached to the chosen Lipschitz lift of a linear-image element.

This is not a descended orthogonal-group spinor norm: it depends on the chosen
lift and on the chosen vector factorization of that lift.
-/
noncomputable def lipschitzLinearImageChosenSpinorNormClass [Invertible (2 : R)]
    (Q : QuadraticForm R M) (g : lipschitzLinearImage Q) :
    Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2) :=
  chosenLipschitzSpinorNormClass Q (lipschitzLinearImageChosenLift Q g)

@[simp]
theorem lipschitzLinearImageChosenSpinorNormClass_sq_eq_one [Invertible (2 : R)]
    (Q : QuadraticForm R M) (g : lipschitzLinearImage Q) :
    lipschitzLinearImageChosenSpinorNormClass Q g ^ 2 = 1 :=
  chosenLipschitzSpinorNormClass_sq_eq_one Q (lipschitzLinearImageChosenLift Q g)

/-- Norm formula for the chosen Lipschitz lift of a linear-image element. -/
theorem star_mul_self_eq_algebraMap_lipschitzLinearImageChosenNormUnit
    [Invertible (2 : R)] (Q : QuadraticForm R M) (g : lipschitzLinearImage Q) :
    star (((lipschitzLinearImageChosenLift Q g : lipschitzGroup Q) :
          (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        (((lipschitzLinearImageChosenLift Q g : lipschitzGroup Q) :
          (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (lipschitzLinearImageChosenNormUnit Q g : R) :=
  star_mul_self_eq_algebraMap_chosenLipschitzNormUnit Q
    (lipschitzLinearImageChosenLift Q g)

end Spinor
