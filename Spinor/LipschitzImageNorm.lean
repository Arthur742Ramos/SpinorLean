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
* `Spinor.LipschitzLinearImageSpinorNormLiftIndependent`
* `Spinor.LipschitzLinearImageSpinorNormDescends`
* `Spinor.lipschitzLinearImageSpinorNormDescends_of_factorizationIndependent`
* `Spinor.lipschitzLinearImageSpinorNormClassHomOfDescends`
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

/--
The lift-independence obligation for the chosen Lipschitz square-class API on the image of
`lipschitzLinearRepresentation`.

This is separate from factorization independence: it says that two Lipschitz-group elements
with the same linear representation have the same chosen square-class value.
-/
structure LipschitzLinearImageSpinorNormLiftIndependent [Invertible (2 : R)]
    (Q : QuadraticForm R M) : Prop where
  eq_of_linearRepresentation_eq : ∀ x y : lipschitzGroup Q,
    lipschitzLinearRepresentation (Q := Q) x =
      lipschitzLinearRepresentation (Q := Q) y →
    chosenLipschitzSpinorNormClass Q x = chosenLipschitzSpinorNormClass Q y

/--
The exact extra obligations needed for the chosen Lipschitz square-class API to descend to a
monoid homomorphism on the image of `lipschitzLinearRepresentation`.

This structure does not assert those obligations globally. It isolates them as theorem-facing
targets: triviality at `1`, multiplicativity on chosen Lipschitz lifts, and independence across
equal linear representations.
-/
structure LipschitzLinearImageSpinorNormDescends [Invertible (2 : R)]
    (Q : QuadraticForm R M) : Prop where
  map_one : chosenLipschitzSpinorNormClass Q (1 : lipschitzGroup Q) = 1
  map_mul : ∀ x y : lipschitzGroup Q,
    chosenLipschitzSpinorNormClass Q (x * y) =
      chosenLipschitzSpinorNormClass Q x * chosenLipschitzSpinorNormClass Q y
  eq_of_linearRepresentation_eq : ∀ x y : lipschitzGroup Q,
    lipschitzLinearRepresentation (Q := Q) x =
      lipschitzLinearRepresentation (Q := Q) y →
    chosenLipschitzSpinorNormClass Q x = chosenLipschitzSpinorNormClass Q y

/--
Under lift independence, the chosen image-level square class agrees with any Lipschitz lift of
the same image element.
-/
theorem lipschitzLinearImageChosenSpinorNormClass_eq_chosenLipschitzSpinorNormClass_of_liftIndependent
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (h : LipschitzLinearImageSpinorNormLiftIndependent Q) (g : lipschitzLinearImage Q)
    (x : lipschitzGroup Q) (hx : lipschitzLinearRepresentation (Q := Q) x = g) :
    lipschitzLinearImageChosenSpinorNormClass Q g =
      chosenLipschitzSpinorNormClass Q x :=
  h.eq_of_linearRepresentation_eq (lipschitzLinearImageChosenLift Q g) x
    ((lipschitzLinearImageChosenLift_spec Q g).trans hx.symm)

/--
Factorization independence plus lift independence imply the chosen-level descent obligations
for the Lipschitz linear image.
-/
theorem lipschitzLinearImageSpinorNormDescends_of_factorizationIndependent
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hfac : LipschitzSpinorNormClassFactorizationIndependent Q)
    (hlift : LipschitzLinearImageSpinorNormLiftIndependent Q) :
    LipschitzLinearImageSpinorNormDescends Q where
  map_one := chosenLipschitzSpinorNormClass_one_of_factorizationIndependent Q hfac
  map_mul := chosenLipschitzSpinorNormClass_mul_of_factorizationIndependent Q hfac
  eq_of_linearRepresentation_eq := hlift.eq_of_linearRepresentation_eq

/--
Under the explicit descent obligations, the chosen image-level square class agrees with any
Lipschitz lift of the same image element.
-/
theorem lipschitzLinearImageChosenSpinorNormClass_eq_chosenLipschitzSpinorNormClass_of_descends
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (h : LipschitzLinearImageSpinorNormDescends Q) (g : lipschitzLinearImage Q)
    (x : lipschitzGroup Q) (hx : lipschitzLinearRepresentation (Q := Q) x = g) :
    lipschitzLinearImageChosenSpinorNormClass Q g =
      chosenLipschitzSpinorNormClass Q x :=
  h.eq_of_linearRepresentation_eq (lipschitzLinearImageChosenLift Q g) x
    ((lipschitzLinearImageChosenLift_spec Q g).trans hx.symm)

/--
If the chosen Lipschitz square-class API satisfies the explicit descent obligations, it becomes
a monoid homomorphism on the Lipschitz linear image.
-/
noncomputable def lipschitzLinearImageSpinorNormClassHomOfDescends
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (h : LipschitzLinearImageSpinorNormDescends Q) :
    lipschitzLinearImage Q →*
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2) where
  toFun := lipschitzLinearImageChosenSpinorNormClass Q
  map_one' := by
    dsimp [lipschitzLinearImageChosenSpinorNormClass]
    have hrep :
        lipschitzLinearRepresentation (Q := Q) (lipschitzLinearImageChosenLift Q 1) =
          lipschitzLinearRepresentation (Q := Q) (1 : lipschitzGroup Q) := by
      rw [lipschitzLinearImageChosenLift_spec]
      exact ((lipschitzLinearRepresentation (Q := Q)).map_one).symm
    exact (h.eq_of_linearRepresentation_eq (lipschitzLinearImageChosenLift Q 1)
      (1 : lipschitzGroup Q) hrep).trans h.map_one
  map_mul' g k := by
    dsimp [lipschitzLinearImageChosenSpinorNormClass]
    have hrep :
        lipschitzLinearRepresentation (Q := Q) (lipschitzLinearImageChosenLift Q (g * k)) =
          lipschitzLinearRepresentation (Q := Q)
            (lipschitzLinearImageChosenLift Q g * lipschitzLinearImageChosenLift Q k) := by
      rw [lipschitzLinearImageChosenLift_spec]
      rw [(lipschitzLinearRepresentation (Q := Q)).map_mul]
      rw [lipschitzLinearImageChosenLift_spec, lipschitzLinearImageChosenLift_spec]
      rfl
    calc
      chosenLipschitzSpinorNormClass Q (lipschitzLinearImageChosenLift Q (g * k)) =
          chosenLipschitzSpinorNormClass Q
            (lipschitzLinearImageChosenLift Q g * lipschitzLinearImageChosenLift Q k) := by
            exact h.eq_of_linearRepresentation_eq
              (lipschitzLinearImageChosenLift Q (g * k))
              (lipschitzLinearImageChosenLift Q g * lipschitzLinearImageChosenLift Q k) hrep
      _ =
          chosenLipschitzSpinorNormClass Q (lipschitzLinearImageChosenLift Q g) *
            chosenLipschitzSpinorNormClass Q (lipschitzLinearImageChosenLift Q k) := by
            exact h.map_mul (lipschitzLinearImageChosenLift Q g)
              (lipschitzLinearImageChosenLift Q k)

@[simp]
theorem lipschitzLinearImageSpinorNormClassHomOfDescends_apply
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (h : LipschitzLinearImageSpinorNormDescends Q) (g : lipschitzLinearImage Q) :
    lipschitzLinearImageSpinorNormClassHomOfDescends Q h g =
      lipschitzLinearImageChosenSpinorNormClass Q g := rfl

end Spinor
