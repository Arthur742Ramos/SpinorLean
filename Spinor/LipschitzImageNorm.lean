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

Factorization independence is proved on the Lipschitz group; independence from the
chosen lift remains the image-level descent issue. The point is to expose a precise
theorem-facing API at the Lipschitz-image level without claiming a descended
orthogonal-group spinor norm.

## Main declarations

* `Spinor.lipschitzLinearImage`
* `Spinor.lipschitzLinearImageChosenLift`
* `Spinor.lipschitzLinearImageChosenNormUnit`
* `Spinor.lipschitzLinearImageChosenSpinorNormClass`
* `Spinor.LipschitzLinearImageSpinorNormLiftIndependent`
* `Spinor.LipschitzLinearImageSpinorNormDescends`
* `Spinor.LipschitzSpinorNormClassTrivialOnLinearKernel`
* `Spinor.LipschitzSpinorNormClassHomTrivialOnLinearKernel`
* `Spinor.lipschitzLinearImageSpinorNormLiftIndependent_of_factorizationIndependent_of_trivialOnLinearKernel`
* `Spinor.lipschitzLinearImageSpinorNormLiftIndependent_of_hom_trivialOnLinearKernel`
* `Spinor.lipschitzLinearImageSpinorNormDescends_of_factorizationIndependent`
* `Spinor.lipschitzLinearImageSpinorNormDescends_of_factorizationIndependent_of_trivialOnLinearKernel`
* `Spinor.lipschitzLinearImageSpinorNormDescends_of_hom_trivialOnLinearKernel`
* `Spinor.lipschitzSpinorNormClassHomOfDescends`
* `Spinor.lipschitzLinearImageSpinorNormClassHomOfDescends`
* `Spinor.lipschitzLinearImageSpinorNormClassHomOfDescends_eq_of_comp_rangeRestrict`
* `Spinor.lipschitzLinearImageSpinorNormClassHomOfHomTrivialOnLinearKernel`
* `Spinor.lipschitzLinearImageSpinorNormClassHomOfFactorizationIndependentOfTrivialOnLinearKernel`
* `Spinor.lipschitzLinearImageSpinorNormClassHomOfFactorizationIndependentOfTrivialOnLinearKernel_eq_of_comp_rangeRestrict`
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
Lipschitz lift of the image element.
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
The kernel-triviality obligation for descending the factorization-independent Lipschitz
spinor norm through the linear representation.

Given factorization independence, the chosen square class is already a monoid homomorphism
on `lipschitzGroup Q`. This structure records the extra condition that this homomorphism is
trivial on the kernel of `lipschitzLinearRepresentation`.
-/
structure LipschitzSpinorNormClassTrivialOnLinearKernel [Invertible (2 : R)]
    (Q : QuadraticForm R M)
    (hfac : LipschitzSpinorNormClassFactorizationIndependent Q) : Prop where
  eq_one_of_linearRepresentation_eq_one : ∀ x : lipschitzGroup Q,
    lipschitzLinearRepresentation (Q := Q) x = 1 →
    lipschitzSpinorNormClassHomOfFactorizationIndependent Q hfac x = 1

/--
The remaining kernel-triviality obligation after the Lipschitz-group spinor-norm hom has been
constructed globally.

This is the condition needed to descend the unconditional Lipschitz-group hom through
`lipschitzLinearRepresentation`.
-/
structure LipschitzSpinorNormClassHomTrivialOnLinearKernel [Invertible (2 : R)]
    (Q : QuadraticForm R M) : Prop where
  eq_one_of_linearRepresentation_eq_one : ∀ x : lipschitzGroup Q,
    lipschitzLinearRepresentation (Q := Q) x = 1 →
    lipschitzSpinorNormClassHom Q x = 1

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
Factorization independence plus kernel-triviality of the induced Lipschitz-group hom imply
lift independence on the image of `lipschitzLinearRepresentation`.
-/
theorem lipschitzLinearImageSpinorNormLiftIndependent_of_factorizationIndependent_of_trivialOnLinearKernel
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hfac : LipschitzSpinorNormClassFactorizationIndependent Q)
    (hker : LipschitzSpinorNormClassTrivialOnLinearKernel Q hfac) :
    LipschitzLinearImageSpinorNormLiftIndependent Q where
  eq_of_linearRepresentation_eq x y hx := by
    let φ := lipschitzSpinorNormClassHomOfFactorizationIndependent Q hfac
    change φ x = φ y
    apply mul_inv_eq_one.mp
    have hlin : lipschitzLinearRepresentation (Q := Q) (x * y⁻¹) = 1 := by
      rw [(lipschitzLinearRepresentation (Q := Q)).map_mul,
        (lipschitzLinearRepresentation (Q := Q)).map_inv, hx]
      exact mul_inv_cancel _
    have hφ : φ (x * y⁻¹) = 1 :=
      hker.eq_one_of_linearRepresentation_eq_one (x * y⁻¹) hlin
    simpa [φ, map_mul, map_inv] using hφ

/--
Kernel-triviality of the global Lipschitz-group hom implies lift independence on the image of
`lipschitzLinearRepresentation`.
-/
theorem lipschitzLinearImageSpinorNormLiftIndependent_of_hom_trivialOnLinearKernel
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hker : LipschitzSpinorNormClassHomTrivialOnLinearKernel Q) :
    LipschitzLinearImageSpinorNormLiftIndependent Q where
  eq_of_linearRepresentation_eq x y hx := by
    let φ := lipschitzSpinorNormClassHom Q
    change φ x = φ y
    apply mul_inv_eq_one.mp
    have hlin : lipschitzLinearRepresentation (Q := Q) (x * y⁻¹) = 1 := by
      rw [(lipschitzLinearRepresentation (Q := Q)).map_mul,
        (lipschitzLinearRepresentation (Q := Q)).map_inv, hx]
      exact mul_inv_cancel _
    have hφ : φ (x * y⁻¹) = 1 :=
      hker.eq_one_of_linearRepresentation_eq_one (x * y⁻¹) hlin
    simpa [φ, map_mul, map_inv] using hφ

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
Factorization independence plus kernel-triviality imply the chosen-level descent obligations
for the Lipschitz linear image.
-/
theorem lipschitzLinearImageSpinorNormDescends_of_factorizationIndependent_of_trivialOnLinearKernel
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hfac : LipschitzSpinorNormClassFactorizationIndependent Q)
    (hker : LipschitzSpinorNormClassTrivialOnLinearKernel Q hfac) :
    LipschitzLinearImageSpinorNormDescends Q :=
  lipschitzLinearImageSpinorNormDescends_of_factorizationIndependent Q hfac
    (lipschitzLinearImageSpinorNormLiftIndependent_of_factorizationIndependent_of_trivialOnLinearKernel
      Q hfac hker)

/--
Kernel-triviality of the global Lipschitz-group hom gives the chosen-level descent obligations
for the Lipschitz linear image.
-/
theorem lipschitzLinearImageSpinorNormDescends_of_hom_trivialOnLinearKernel
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hker : LipschitzSpinorNormClassHomTrivialOnLinearKernel Q) :
    LipschitzLinearImageSpinorNormDescends Q :=
  lipschitzLinearImageSpinorNormDescends_of_factorizationIndependent Q
    (lipschitzSpinorNormClassFactorizationIndependent Q)
    (lipschitzLinearImageSpinorNormLiftIndependent_of_hom_trivialOnLinearKernel Q hker)

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
If the chosen Lipschitz square-class API satisfies the explicit descent obligations, it is
also a monoid homomorphism on the Lipschitz group before passing to the linear image.
-/
noncomputable def lipschitzSpinorNormClassHomOfDescends
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (h : LipschitzLinearImageSpinorNormDescends Q) :
    lipschitzGroup Q →*
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2) where
  toFun := chosenLipschitzSpinorNormClass Q
  map_one' := h.map_one
  map_mul' := h.map_mul

@[simp]
theorem lipschitzSpinorNormClassHomOfDescends_apply
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (h : LipschitzLinearImageSpinorNormDescends Q) (x : lipschitzGroup Q) :
    lipschitzSpinorNormClassHomOfDescends Q h x =
      chosenLipschitzSpinorNormClass Q x := rfl

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

@[simp]
theorem lipschitzLinearImageSpinorNormClassHomOfDescends_rangeRestrict
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (h : LipschitzLinearImageSpinorNormDescends Q) (x : lipschitzGroup Q) :
    lipschitzLinearImageSpinorNormClassHomOfDescends Q h
        ((lipschitzLinearRepresentation (Q := Q)).rangeRestrict x) =
        chosenLipschitzSpinorNormClass Q x := by
  exact lipschitzLinearImageChosenSpinorNormClass_eq_chosenLipschitzSpinorNormClass_of_descends
    Q h ((lipschitzLinearRepresentation (Q := Q)).rangeRestrict x) x
    (by simp)

/--
The image-level hom pulls back along the range-restricted Lipschitz linear representation to
the corresponding descended hom on the Lipschitz group.
-/
theorem lipschitzLinearImageSpinorNormClassHomOfDescends_comp_rangeRestrict
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (h : LipschitzLinearImageSpinorNormDescends Q) :
    (lipschitzLinearImageSpinorNormClassHomOfDescends Q h).comp
        (lipschitzLinearRepresentation (Q := Q)).rangeRestrict =
      lipschitzSpinorNormClassHomOfDescends Q h := by
  ext x
  exact lipschitzLinearImageSpinorNormClassHomOfDescends_rangeRestrict Q h x

/--
The descended image-level hom is uniquely determined by its pullback along the
range-restricted Lipschitz linear representation.
-/
theorem lipschitzLinearImageSpinorNormClassHomOfDescends_eq_of_comp_rangeRestrict
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (h : LipschitzLinearImageSpinorNormDescends Q)
    (ψ : lipschitzLinearImage Q →*
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2))
    (hψ : ψ.comp (lipschitzLinearRepresentation (Q := Q)).rangeRestrict =
      lipschitzSpinorNormClassHomOfDescends Q h) :
    ψ = lipschitzLinearImageSpinorNormClassHomOfDescends Q h := by
  ext g
  rcases (lipschitzLinearRepresentation (Q := Q)).rangeRestrict_surjective g with ⟨x, rfl⟩
  have hpoint := congrArg (fun φ => φ x) hψ
  calc
    ψ ((lipschitzLinearRepresentation (Q := Q)).rangeRestrict x) =
        chosenLipschitzSpinorNormClass Q x := by
        simpa [MonoidHom.comp_apply] using hpoint
    _ =
        lipschitzLinearImageSpinorNormClassHomOfDescends Q h
          ((lipschitzLinearRepresentation (Q := Q)).rangeRestrict x) := by
        exact (lipschitzLinearImageSpinorNormClassHomOfDescends_rangeRestrict Q h x).symm

/--
Kernel-triviality of the global Lipschitz-group hom directly gives the image-level
spinor-norm square-class monoid hom.
-/
noncomputable def lipschitzLinearImageSpinorNormClassHomOfHomTrivialOnLinearKernel
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hker : LipschitzSpinorNormClassHomTrivialOnLinearKernel Q) :
    lipschitzLinearImage Q →*
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2) :=
  lipschitzLinearImageSpinorNormClassHomOfDescends Q
    (lipschitzLinearImageSpinorNormDescends_of_hom_trivialOnLinearKernel Q hker)

@[simp]
theorem lipschitzLinearImageSpinorNormClassHomOfHomTrivialOnLinearKernel_apply
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hker : LipschitzSpinorNormClassHomTrivialOnLinearKernel Q)
    (g : lipschitzLinearImage Q) :
    lipschitzLinearImageSpinorNormClassHomOfHomTrivialOnLinearKernel Q hker g =
      lipschitzLinearImageChosenSpinorNormClass Q g := rfl

@[simp]
theorem lipschitzLinearImageSpinorNormClassHomOfHomTrivialOnLinearKernel_rangeRestrict
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hker : LipschitzSpinorNormClassHomTrivialOnLinearKernel Q)
    (x : lipschitzGroup Q) :
    lipschitzLinearImageSpinorNormClassHomOfHomTrivialOnLinearKernel Q hker
        ((lipschitzLinearRepresentation (Q := Q)).rangeRestrict x) =
      chosenLipschitzSpinorNormClass Q x := by
  exact lipschitzLinearImageSpinorNormClassHomOfDescends_rangeRestrict Q
    (lipschitzLinearImageSpinorNormDescends_of_hom_trivialOnLinearKernel Q hker) x

/--
The image-level hom obtained from kernel-triviality of the global Lipschitz-group hom pulls
back to the global Lipschitz-group hom.
-/
theorem lipschitzLinearImageSpinorNormClassHomOfHomTrivialOnLinearKernel_comp_rangeRestrict
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hker : LipschitzSpinorNormClassHomTrivialOnLinearKernel Q) :
    (lipschitzLinearImageSpinorNormClassHomOfHomTrivialOnLinearKernel Q hker).comp
        (lipschitzLinearRepresentation (Q := Q)).rangeRestrict =
      lipschitzSpinorNormClassHom Q := by
  ext x
  exact lipschitzLinearImageSpinorNormClassHomOfHomTrivialOnLinearKernel_rangeRestrict
    Q hker x

/--
The image-level hom obtained from kernel-triviality of the global Lipschitz-group hom is the
unique image-level hom whose pullback is the global Lipschitz-group hom.
-/
theorem lipschitzLinearImageSpinorNormClassHomOfHomTrivialOnLinearKernel_eq_of_comp_rangeRestrict
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hker : LipschitzSpinorNormClassHomTrivialOnLinearKernel Q)
    (ψ : lipschitzLinearImage Q →*
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2))
    (hψ : ψ.comp (lipschitzLinearRepresentation (Q := Q)).rangeRestrict =
      lipschitzSpinorNormClassHom Q) :
    ψ = lipschitzLinearImageSpinorNormClassHomOfHomTrivialOnLinearKernel Q hker := by
  ext g
  rcases (lipschitzLinearRepresentation (Q := Q)).rangeRestrict_surjective g with ⟨x, rfl⟩
  have hpoint := congrArg (fun φ => φ x) hψ
  calc
    ψ ((lipschitzLinearRepresentation (Q := Q)).rangeRestrict x) =
        chosenLipschitzSpinorNormClass Q x := by
        simpa [MonoidHom.comp_apply] using hpoint
    _ =
        lipschitzLinearImageSpinorNormClassHomOfHomTrivialOnLinearKernel Q hker
          ((lipschitzLinearRepresentation (Q := Q)).rangeRestrict x) := by
        exact (lipschitzLinearImageSpinorNormClassHomOfHomTrivialOnLinearKernel_rangeRestrict
          Q hker x).symm

/--
Factorization independence plus kernel-triviality directly give the image-level
spinor-norm square-class monoid hom.

This remains conditional on the two explicit global obligations; it is a convenience wrapper
around the descent package and does not prove those obligations globally.
-/
noncomputable def lipschitzLinearImageSpinorNormClassHomOfFactorizationIndependentOfTrivialOnLinearKernel
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hfac : LipschitzSpinorNormClassFactorizationIndependent Q)
    (hker : LipschitzSpinorNormClassTrivialOnLinearKernel Q hfac) :
    lipschitzLinearImage Q →*
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2) :=
  lipschitzLinearImageSpinorNormClassHomOfDescends Q
    (lipschitzLinearImageSpinorNormDescends_of_factorizationIndependent_of_trivialOnLinearKernel
      Q hfac hker)

@[simp]
theorem lipschitzLinearImageSpinorNormClassHomOfFactorizationIndependentOfTrivialOnLinearKernel_apply
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hfac : LipschitzSpinorNormClassFactorizationIndependent Q)
    (hker : LipschitzSpinorNormClassTrivialOnLinearKernel Q hfac)
    (g : lipschitzLinearImage Q) :
    lipschitzLinearImageSpinorNormClassHomOfFactorizationIndependentOfTrivialOnLinearKernel
        Q hfac hker g =
      lipschitzLinearImageChosenSpinorNormClass Q g := rfl

@[simp]
theorem
    lipschitzLinearImageSpinorNormClassHomOfFactorizationIndependentOfTrivialOnLinearKernel_rangeRestrict
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hfac : LipschitzSpinorNormClassFactorizationIndependent Q)
    (hker : LipschitzSpinorNormClassTrivialOnLinearKernel Q hfac)
    (x : lipschitzGroup Q) :
    lipschitzLinearImageSpinorNormClassHomOfFactorizationIndependentOfTrivialOnLinearKernel
        Q hfac hker ((lipschitzLinearRepresentation (Q := Q)).rangeRestrict x) =
      chosenLipschitzSpinorNormClass Q x := by
  exact lipschitzLinearImageSpinorNormClassHomOfDescends_rangeRestrict Q
    (lipschitzLinearImageSpinorNormDescends_of_factorizationIndependent_of_trivialOnLinearKernel
      Q hfac hker) x

/--
The direct conditional image-level hom has the expected pullback: after composing with the
range-restricted Lipschitz linear representation, it is the factorization-independent
Lipschitz-group spinor-norm hom.
-/
theorem
    lipschitzLinearImageSpinorNormClassHomOfFactorizationIndependentOfTrivialOnLinearKernel_comp_rangeRestrict
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hfac : LipschitzSpinorNormClassFactorizationIndependent Q)
    (hker : LipschitzSpinorNormClassTrivialOnLinearKernel Q hfac) :
    (lipschitzLinearImageSpinorNormClassHomOfFactorizationIndependentOfTrivialOnLinearKernel
        Q hfac hker).comp (lipschitzLinearRepresentation (Q := Q)).rangeRestrict =
      lipschitzSpinorNormClassHomOfFactorizationIndependent Q hfac := by
  ext x
  exact
    lipschitzLinearImageSpinorNormClassHomOfFactorizationIndependentOfTrivialOnLinearKernel_rangeRestrict
      Q hfac hker x

/--
The direct conditional image-level hom is the unique image-level hom whose pullback along
`lipschitzLinearRepresentation.rangeRestrict` is the factorization-independent
Lipschitz-group spinor-norm hom.
-/
theorem
    lipschitzLinearImageSpinorNormClassHomOfFactorizationIndependentOfTrivialOnLinearKernel_eq_of_comp_rangeRestrict
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hfac : LipschitzSpinorNormClassFactorizationIndependent Q)
    (hker : LipschitzSpinorNormClassTrivialOnLinearKernel Q hfac)
    (ψ : lipschitzLinearImage Q →*
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2))
    (hψ : ψ.comp (lipschitzLinearRepresentation (Q := Q)).rangeRestrict =
      lipschitzSpinorNormClassHomOfFactorizationIndependent Q hfac) :
    ψ =
      lipschitzLinearImageSpinorNormClassHomOfFactorizationIndependentOfTrivialOnLinearKernel
        Q hfac hker := by
  ext g
  rcases (lipschitzLinearRepresentation (Q := Q)).rangeRestrict_surjective g with ⟨x, rfl⟩
  have hpoint := congrArg (fun φ => φ x) hψ
  calc
    ψ ((lipschitzLinearRepresentation (Q := Q)).rangeRestrict x) =
        chosenLipschitzSpinorNormClass Q x := by
        simpa [MonoidHom.comp_apply] using hpoint
    _ =
        lipschitzLinearImageSpinorNormClassHomOfFactorizationIndependentOfTrivialOnLinearKernel
          Q hfac hker ((lipschitzLinearRepresentation (Q := Q)).rangeRestrict x) := by
        exact
          (lipschitzLinearImageSpinorNormClassHomOfFactorizationIndependentOfTrivialOnLinearKernel_rangeRestrict
            Q hfac hker x).symm

end Spinor
