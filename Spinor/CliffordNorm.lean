/-
  Clifford norm formulas for products of vectors.

  This module gives the global Clifford-algebra calculation behind the
  reflection-product form of the spinor norm. It also packages those products as
  elements of Mathlib's `lipschitzGroup`. The group-level bridge is still a
  chosen-factorization API: it does not assert independence of a
  Cartan-Dieudonne decomposition or descent to a full orthogonal-group
  spinor-norm homomorphism.
-/

import Spinor.Mathlib
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Clifford norm formulas

For a list of vectors, the Clifford conjugation norm of the product of their
`ι`-images is the scalar product of the signed quadratic values. For a product
of invertible vectors, this scalar is also packaged as a unit and as its
square-class quotient, and as a chosen-factorization element of the Lipschitz
group. These declarations provide a global Clifford/Lipschitz substrate for
later spinor-norm developments without claiming an orthogonal-group spinor-norm
API.

## Main declarations

* `Spinor.cliffordVectorProduct`
* `Spinor.cliffordVectorProductNormScalar`
* `Spinor.star_cliffordVectorProduct_mul_cliffordVectorProduct`
* `Spinor.cliffordInvertibleVectorProductNormUnit`
* `Spinor.cliffordInvertibleVectorLipschitz`
* `Spinor.cliffordInvertibleVectorProductLipschitz`
* `Spinor.cliffordInvertibleVectorProductSpinorNormClass`
* `Spinor.cliffordInvertibleVectorProductSpinorNormClass_perm`
* `Spinor.cliffordInvertibleVectorProductSpinorNormClass_cons_self_cons`
* `Spinor.cliffordInvertibleVectorProductSpinorNormClass_append_self`
* `Spinor.cliffordInvertibleVectorProductSpinorNormClass_append_append_self_append`
* `Spinor.cliffordInvertibleVectorProductSpinorNormClass_append_append_middle_self_append`
* `Spinor.cliffordInvertibleVectorProductSpinorNormClass_eq_of_perm_append_cons_self_cons`
* `Spinor.cliffordInvertibleVectorProductSpinorNormClass_eq_of_perm_append_append_middle_self_append`
-/

namespace Spinor

universe uR uM

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- The Clifford product of the `ι`-images of a list of vectors. -/
def cliffordVectorProduct (Q : QuadraticForm R M) (l : List M) : CliffordAlgebra Q :=
  (l.map (CliffordAlgebra.ι Q)).prod

@[simp]
theorem cliffordVectorProduct_nil (Q : QuadraticForm R M) :
    cliffordVectorProduct Q [] = 1 := rfl

@[simp]
theorem cliffordVectorProduct_cons (Q : QuadraticForm R M) (m : M) (l : List M) :
    cliffordVectorProduct Q (m :: l) =
      CliffordAlgebra.ι Q m * cliffordVectorProduct Q l := rfl

@[simp]
theorem cliffordVectorProduct_append (Q : QuadraticForm R M) (l₁ l₂ : List M) :
    cliffordVectorProduct Q (l₁ ++ l₂) =
      cliffordVectorProduct Q l₁ * cliffordVectorProduct Q l₂ := by
  simp [cliffordVectorProduct, List.map_append]

/-- The scalar Clifford norm of a list of vectors, with the sign convention coming from
`star (ι Q m) = -ι Q m`. -/
def cliffordVectorProductNormScalar (Q : QuadraticForm R M) (l : List M) : R :=
  (l.map fun m => -Q m).prod

@[simp]
theorem cliffordVectorProductNormScalar_nil (Q : QuadraticForm R M) :
    cliffordVectorProductNormScalar Q [] = 1 := rfl

@[simp]
theorem cliffordVectorProductNormScalar_cons (Q : QuadraticForm R M) (m : M) (l : List M) :
    cliffordVectorProductNormScalar Q (m :: l) =
      (-Q m) * cliffordVectorProductNormScalar Q l := rfl

@[simp]
theorem cliffordVectorProductNormScalar_append (Q : QuadraticForm R M) (l₁ l₂ : List M) :
    cliffordVectorProductNormScalar Q (l₁ ++ l₂) =
      cliffordVectorProductNormScalar Q l₁ * cliffordVectorProductNormScalar Q l₂ := by
  simp [cliffordVectorProductNormScalar, List.map_append]

theorem cliffordVectorProductNormScalar_perm (Q : QuadraticForm R M)
    {l₁ l₂ : List M} (h : l₁.Perm l₂) :
    cliffordVectorProductNormScalar Q l₁ = cliffordVectorProductNormScalar Q l₂ := by
  simpa [cliffordVectorProductNormScalar] using
    (h.map fun m => -Q m).prod_eq

@[simp]
theorem cliffordVectorProductNormScalar_reverse (Q : QuadraticForm R M) (l : List M) :
    cliffordVectorProductNormScalar Q l.reverse = cliffordVectorProductNormScalar Q l :=
  cliffordVectorProductNormScalar_perm Q l.reverse_perm

/-- The Clifford conjugation norm of a product of vector generators is the scalar product of the
signed quadratic values. -/
theorem star_cliffordVectorProduct_mul_cliffordVectorProduct
    (Q : QuadraticForm R M) (l : List M) :
    star (cliffordVectorProduct Q l) * cliffordVectorProduct Q l =
      algebraMap R (CliffordAlgebra Q) (cliffordVectorProductNormScalar Q l) := by
  induction l with
  | nil =>
      simp [cliffordVectorProduct, cliffordVectorProductNormScalar]
  | cons m l ih =>
      let P : CliffordAlgebra Q := cliffordVectorProduct Q l
      have hnorm :
          (-CliffordAlgebra.ι Q m) * CliffordAlgebra.ι Q m =
            algebraMap R (CliffordAlgebra Q) (-Q m) := by
        rw [neg_mul, CliffordAlgebra.ι_sq_scalar]
        simp
      calc
        star (cliffordVectorProduct Q (m :: l)) * cliffordVectorProduct Q (m :: l)
            = (star P * (-CliffordAlgebra.ι Q m)) *
                (CliffordAlgebra.ι Q m * P) := by
              simp [P]
        _ = star P *
                ((-CliffordAlgebra.ι Q m) * CliffordAlgebra.ι Q m) * P := by
              rw [mul_assoc, ← mul_assoc (-CliffordAlgebra.ι Q m) (CliffordAlgebra.ι Q m) P,
                ← mul_assoc]
        _ = star (cliffordVectorProduct Q l) *
              algebraMap R (CliffordAlgebra Q) (-Q m) *
              cliffordVectorProduct Q l := by
              simp [P, hnorm]
        _ = algebraMap R (CliffordAlgebra Q) (-Q m) *
              (star (cliffordVectorProduct Q l) * cliffordVectorProduct Q l) := by
              rw [← Algebra.commutes (-Q m) (star (cliffordVectorProduct Q l))]
              rw [mul_assoc]
        _ = algebraMap R (CliffordAlgebra Q) (-Q m) *
              algebraMap R (CliffordAlgebra Q) (cliffordVectorProductNormScalar Q l) := by
              rw [ih]
        _ = algebraMap R (CliffordAlgebra Q)
              (cliffordVectorProductNormScalar Q (m :: l)) := by
              simp [cliffordVectorProductNormScalar]

/-- A vector together with evidence that its quadratic value is a unit. -/
abbrev InvertibleQuadraticVector (Q : QuadraticForm R M) :=
  {m : M // IsUnit (Q m)}

/-- The signed quadratic unit attached to an invertible vector. -/
noncomputable def cliffordInvertibleVectorNormUnit (Q : QuadraticForm R M)
    (m : InvertibleQuadraticVector Q) : Rˣ :=
  -m.2.unit

@[simp]
theorem coe_cliffordInvertibleVectorNormUnit (Q : QuadraticForm R M)
    (m : InvertibleQuadraticVector Q) :
    (cliffordInvertibleVectorNormUnit Q m : R) = -Q m.1 := by
  simp [cliffordInvertibleVectorNormUnit, IsUnit.unit_spec]

/-- The Clifford norm unit of a product of invertible vectors. -/
noncomputable def cliffordInvertibleVectorProductNormUnit (Q : QuadraticForm R M)
    (l : List (InvertibleQuadraticVector Q)) : Rˣ :=
  (l.map (cliffordInvertibleVectorNormUnit Q)).prod

@[simp]
theorem cliffordInvertibleVectorProductNormUnit_nil (Q : QuadraticForm R M) :
    cliffordInvertibleVectorProductNormUnit Q [] = 1 := rfl

@[simp]
theorem cliffordInvertibleVectorProductNormUnit_cons (Q : QuadraticForm R M)
    (m : InvertibleQuadraticVector Q) (l : List (InvertibleQuadraticVector Q)) :
    cliffordInvertibleVectorProductNormUnit Q (m :: l) =
      cliffordInvertibleVectorNormUnit Q m *
        cliffordInvertibleVectorProductNormUnit Q l := rfl

@[simp]
theorem cliffordInvertibleVectorProductNormUnit_append (Q : QuadraticForm R M)
    (l₁ l₂ : List (InvertibleQuadraticVector Q)) :
    cliffordInvertibleVectorProductNormUnit Q (l₁ ++ l₂) =
      cliffordInvertibleVectorProductNormUnit Q l₁ *
        cliffordInvertibleVectorProductNormUnit Q l₂ := by
  simp [cliffordInvertibleVectorProductNormUnit, List.map_append]

theorem cliffordInvertibleVectorProductNormUnit_perm (Q : QuadraticForm R M)
    {l₁ l₂ : List (InvertibleQuadraticVector Q)} (h : l₁.Perm l₂) :
    cliffordInvertibleVectorProductNormUnit Q l₁ =
      cliffordInvertibleVectorProductNormUnit Q l₂ := by
  simpa [cliffordInvertibleVectorProductNormUnit] using
    (h.map (cliffordInvertibleVectorNormUnit Q)).prod_eq

@[simp]
theorem cliffordInvertibleVectorProductNormUnit_reverse (Q : QuadraticForm R M)
    (l : List (InvertibleQuadraticVector Q)) :
    cliffordInvertibleVectorProductNormUnit Q l.reverse =
      cliffordInvertibleVectorProductNormUnit Q l :=
  cliffordInvertibleVectorProductNormUnit_perm Q l.reverse_perm

@[simp]
theorem coe_cliffordInvertibleVectorProductNormUnit (Q : QuadraticForm R M)
    (l : List (InvertibleQuadraticVector Q)) :
    (cliffordInvertibleVectorProductNormUnit Q l : R) =
      cliffordVectorProductNormScalar Q (l.map Subtype.val) := by
  induction l with
  | nil =>
      simp [cliffordInvertibleVectorProductNormUnit, cliffordVectorProductNormScalar]
  | cons m l ih =>
      change
        ((cliffordInvertibleVectorNormUnit Q m *
            cliffordInvertibleVectorProductNormUnit Q l : Rˣ) : R) =
          (-Q m.1) * cliffordVectorProductNormScalar Q (l.map Subtype.val)
      rw [Units.val_mul, coe_cliffordInvertibleVectorNormUnit, ih]

@[simp]
theorem cliffordVectorProduct_map_invertibleQuadraticVector_val
    (Q : QuadraticForm R M) (l : List (InvertibleQuadraticVector Q)) :
    cliffordVectorProduct Q (l.map Subtype.val) =
      (l.map fun m => CliffordAlgebra.ι Q m.1).prod := by
  induction l with
  | nil => simp [cliffordVectorProduct]
  | cons m l ih => simp [cliffordVectorProduct]

/-- The Clifford conjugation norm formula for a product of invertible vectors, stated with the
scalar packaged as a unit. -/
theorem star_cliffordInvertibleVectorProduct_mul_cliffordInvertibleVectorProduct
    (Q : QuadraticForm R M) (l : List (InvertibleQuadraticVector Q)) :
    star (cliffordVectorProduct Q (l.map Subtype.val)) *
        cliffordVectorProduct Q (l.map Subtype.val) =
      algebraMap R (CliffordAlgebra Q)
        (cliffordInvertibleVectorProductNormUnit Q l : R) := by
  simpa using
    star_cliffordVectorProduct_mul_cliffordVectorProduct
      (Q := Q) (l := l.map Subtype.val)

/-- The Clifford unit attached to an invertible quadratic vector. -/
noncomputable def cliffordInvertibleVectorUnit (Q : QuadraticForm R M)
    (m : InvertibleQuadraticVector Q) : (CliffordAlgebra Q)ˣ :=
  (CliffordAlgebra.isUnit_ι_of_isUnit (Q := Q) m.2).unit

@[simp]
theorem coe_cliffordInvertibleVectorUnit (Q : QuadraticForm R M)
    (m : InvertibleQuadraticVector Q) :
    ((cliffordInvertibleVectorUnit Q m : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q) =
      CliffordAlgebra.ι Q m.1 :=
  IsUnit.unit_spec <| CliffordAlgebra.isUnit_ι_of_isUnit (Q := Q) m.2

/-- An invertible quadratic vector, viewed as a generator of the Lipschitz group. -/
noncomputable def cliffordInvertibleVectorLipschitz (Q : QuadraticForm R M)
    (m : InvertibleQuadraticVector Q) : lipschitzGroup Q :=
  ⟨cliffordInvertibleVectorUnit Q m, by
    unfold lipschitzGroup
    exact Subgroup.subset_closure <| by
      change
        (((cliffordInvertibleVectorUnit Q m : (CliffordAlgebra Q)ˣ) :
            CliffordAlgebra Q)) ∈ Set.range (CliffordAlgebra.ι Q)
      exact ⟨m.1, coe_cliffordInvertibleVectorUnit Q m⟩⟩

@[simp]
theorem coe_cliffordInvertibleVectorLipschitz (Q : QuadraticForm R M)
    (m : InvertibleQuadraticVector Q) :
    (((cliffordInvertibleVectorLipschitz Q m : lipschitzGroup Q) :
        (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q m.1 :=
  coe_cliffordInvertibleVectorUnit Q m

/-- The Lipschitz-group element represented by a product of invertible vector generators. -/
noncomputable def cliffordInvertibleVectorProductLipschitz (Q : QuadraticForm R M)
    (l : List (InvertibleQuadraticVector Q)) : lipschitzGroup Q :=
  (l.map (cliffordInvertibleVectorLipschitz Q)).prod

@[simp]
theorem cliffordInvertibleVectorProductLipschitz_nil (Q : QuadraticForm R M) :
    cliffordInvertibleVectorProductLipschitz Q [] = 1 := rfl

@[simp]
theorem cliffordInvertibleVectorProductLipschitz_cons (Q : QuadraticForm R M)
    (m : InvertibleQuadraticVector Q) (l : List (InvertibleQuadraticVector Q)) :
    cliffordInvertibleVectorProductLipschitz Q (m :: l) =
      cliffordInvertibleVectorLipschitz Q m *
        cliffordInvertibleVectorProductLipschitz Q l := rfl

@[simp]
theorem cliffordInvertibleVectorProductLipschitz_append (Q : QuadraticForm R M)
    (l₁ l₂ : List (InvertibleQuadraticVector Q)) :
    cliffordInvertibleVectorProductLipschitz Q (l₁ ++ l₂) =
      cliffordInvertibleVectorProductLipschitz Q l₁ *
        cliffordInvertibleVectorProductLipschitz Q l₂ := by
  simp [cliffordInvertibleVectorProductLipschitz, List.map_append]

@[simp]
theorem coe_cliffordInvertibleVectorProductLipschitz (Q : QuadraticForm R M)
    (l : List (InvertibleQuadraticVector Q)) :
    (((cliffordInvertibleVectorProductLipschitz Q l : lipschitzGroup Q) :
        (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      cliffordVectorProduct Q (l.map Subtype.val) := by
  induction l with
  | nil =>
      simp [cliffordInvertibleVectorProductLipschitz, cliffordVectorProduct]
  | cons m l ih =>
      change
        CliffordAlgebra.ι Q m.1 *
            (((cliffordInvertibleVectorProductLipschitz Q l : lipschitzGroup Q) :
              (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
          CliffordAlgebra.ι Q m.1 * cliffordVectorProduct Q (l.map Subtype.val)
      rw [ih]

/-- The Clifford conjugation norm formula for the corresponding Lipschitz-group product. -/
theorem star_cliffordInvertibleVectorProductLipschitz_mul_self
    (Q : QuadraticForm R M) (l : List (InvertibleQuadraticVector Q)) :
    star (((cliffordInvertibleVectorProductLipschitz Q l : lipschitzGroup Q) :
          (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        (((cliffordInvertibleVectorProductLipschitz Q l : lipschitzGroup Q) :
          (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q)
        (cliffordInvertibleVectorProductNormUnit Q l : R) := by
  simpa using star_cliffordInvertibleVectorProduct_mul_cliffordInvertibleVectorProduct
    (Q := Q) (l := l)

/-- The Clifford conjugation norm formula for a single Lipschitz vector generator. -/
theorem star_cliffordInvertibleVectorLipschitz_mul_self
    (Q : QuadraticForm R M) (m : InvertibleQuadraticVector Q) :
    star (((cliffordInvertibleVectorLipschitz Q m : lipschitzGroup Q) :
          (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        (((cliffordInvertibleVectorLipschitz Q m : lipschitzGroup Q) :
          (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (cliffordInvertibleVectorNormUnit Q m : R) := by
  have h := star_cliffordInvertibleVectorProductLipschitz_mul_self (Q := Q) [m]
  simpa using h

/-- The square-class of the signed quadratic unit attached to a product of invertible vectors.
This is the product-level spinor-norm invariant; no independence from a chosen vector
decomposition is asserted here. -/
noncomputable def cliffordInvertibleVectorProductSpinorNormClass (Q : QuadraticForm R M)
    (l : List (InvertibleQuadraticVector Q)) :
    Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2) :=
  cliffordInvertibleVectorProductNormUnit Q l

@[simp]
theorem cliffordInvertibleVectorProductSpinorNormClass_nil (Q : QuadraticForm R M) :
    cliffordInvertibleVectorProductSpinorNormClass Q [] = 1 := rfl

@[simp]
theorem cliffordInvertibleVectorProductSpinorNormClass_cons (Q : QuadraticForm R M)
    (m : InvertibleQuadraticVector Q) (l : List (InvertibleQuadraticVector Q)) :
    cliffordInvertibleVectorProductSpinorNormClass Q (m :: l) =
      (cliffordInvertibleVectorNormUnit Q m :
        Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2)) *
        cliffordInvertibleVectorProductSpinorNormClass Q l := by
  rfl

@[simp]
theorem cliffordInvertibleVectorProductSpinorNormClass_append (Q : QuadraticForm R M)
    (l₁ l₂ : List (InvertibleQuadraticVector Q)) :
    cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l₂) =
      cliffordInvertibleVectorProductSpinorNormClass Q l₁ *
        cliffordInvertibleVectorProductSpinorNormClass Q l₂ := by
  simp [cliffordInvertibleVectorProductSpinorNormClass]

theorem cliffordInvertibleVectorProductSpinorNormClass_perm (Q : QuadraticForm R M)
    {l₁ l₂ : List (InvertibleQuadraticVector Q)} (h : l₁.Perm l₂) :
    cliffordInvertibleVectorProductSpinorNormClass Q l₁ =
      cliffordInvertibleVectorProductSpinorNormClass Q l₂ := by
  simp [cliffordInvertibleVectorProductSpinorNormClass,
    cliffordInvertibleVectorProductNormUnit_perm Q h]

@[simp]
theorem cliffordInvertibleVectorProductSpinorNormClass_reverse (Q : QuadraticForm R M)
    (l : List (InvertibleQuadraticVector Q)) :
    cliffordInvertibleVectorProductSpinorNormClass Q l.reverse =
      cliffordInvertibleVectorProductSpinorNormClass Q l :=
  cliffordInvertibleVectorProductSpinorNormClass_perm Q l.reverse_perm

theorem cliffordInvertibleVectorNormUnit_sq_spinorNormClass_eq_one
    (Q : QuadraticForm R M) (m : InvertibleQuadraticVector Q) :
    ((cliffordInvertibleVectorNormUnit Q m ^ 2 : Rˣ) :
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2)) = 1 := by
  rw [QuotientGroup.eq_one_iff]
  exact ⟨cliffordInvertibleVectorNormUnit Q m, rfl⟩

theorem cliffordInvertibleVectorProductNormUnit_sq_spinorNormClass_eq_one
    (Q : QuadraticForm R M) (l : List (InvertibleQuadraticVector Q)) :
    ((cliffordInvertibleVectorProductNormUnit Q l ^ 2 : Rˣ) :
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2)) = 1 := by
  rw [QuotientGroup.eq_one_iff]
  exact ⟨cliffordInvertibleVectorProductNormUnit Q l, rfl⟩

theorem cliffordInvertibleVectorProductSpinorNormClass_sq_eq_one
    (Q : QuadraticForm R M) (l : List (InvertibleQuadraticVector Q)) :
    cliffordInvertibleVectorProductSpinorNormClass Q l ^ 2 = 1 := by
  let u := cliffordInvertibleVectorProductNormUnit Q l
  change ((u : Rˣ) :
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2)) ^ 2 = 1
  change ((u ^ 2 : Rˣ) :
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2)) = 1
  exact cliffordInvertibleVectorProductNormUnit_sq_spinorNormClass_eq_one Q l

/--
A Lipschitz element together with a chosen decomposition as a product of invertible vectors.

This is the group-level replacement for bare vector lists. It intentionally stores the
factorization data; no independence theorem for two different decompositions is claimed here.
-/
structure LipschitzVectorFactorization (Q : QuadraticForm R M) (x : lipschitzGroup Q) where
  factors : List (InvertibleQuadraticVector Q)
  product_eq : cliffordInvertibleVectorProductLipschitz Q factors = x

namespace LipschitzVectorFactorization

variable {Q : QuadraticForm R M}

/-- The square-class spinor norm attached to a chosen Lipschitz vector factorization. -/
noncomputable def spinorNormClass {x : lipschitzGroup Q}
    (F : LipschitzVectorFactorization Q x) :
    Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2) :=
  cliffordInvertibleVectorProductSpinorNormClass Q F.factors

@[simp]
theorem spinorNormClass_sq_eq_one {x : lipschitzGroup Q}
    (F : LipschitzVectorFactorization Q x) :
    F.spinorNormClass ^ 2 = 1 :=
  cliffordInvertibleVectorProductSpinorNormClass_sq_eq_one Q F.factors

/-- Norm formula for the group element underlying a chosen Lipschitz vector factorization. -/
theorem star_mul_self_eq_algebraMap_normUnit {x : lipschitzGroup Q}
    (F : LipschitzVectorFactorization Q x) :
    star (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q)
        (cliffordInvertibleVectorProductNormUnit Q F.factors : R) := by
  have hx :
      (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        (((cliffordInvertibleVectorProductLipschitz Q F.factors : lipschitzGroup Q) :
          (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
    exact congrArg
      (fun y : lipschitzGroup Q => (((y : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q)) F.product_eq.symm
  rw [hx]
  exact star_cliffordInvertibleVectorProductLipschitz_mul_self (Q := Q) F.factors

end LipschitzVectorFactorization

@[simp]
theorem cliffordInvertibleVectorProductSpinorNormClass_cons_self_cons
    (Q : QuadraticForm R M) (m : InvertibleQuadraticVector Q)
    (l : List (InvertibleQuadraticVector Q)) :
    cliffordInvertibleVectorProductSpinorNormClass Q (m :: m :: l) =
      cliffordInvertibleVectorProductSpinorNormClass Q l := by
  rw [cliffordInvertibleVectorProductSpinorNormClass_cons,
    cliffordInvertibleVectorProductSpinorNormClass_cons]
  let u := cliffordInvertibleVectorNormUnit Q m
  rw [← mul_assoc]
  change ((u * u : Rˣ) :
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2)) *
        cliffordInvertibleVectorProductSpinorNormClass Q l =
      cliffordInvertibleVectorProductSpinorNormClass Q l
  rw [show u * u = u ^ 2 by rw [pow_two],
    cliffordInvertibleVectorNormUnit_sq_spinorNormClass_eq_one]
  exact one_mul (cliffordInvertibleVectorProductSpinorNormClass Q l)

@[simp]
theorem cliffordInvertibleVectorProductSpinorNormClass_append_cons_self_cons
    (Q : QuadraticForm R M) (l₁ l₂ : List (InvertibleQuadraticVector Q))
    (m : InvertibleQuadraticVector Q) :
    cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ m :: m :: l₂) =
      cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l₂) := by
  rw [cliffordInvertibleVectorProductSpinorNormClass_append,
    cliffordInvertibleVectorProductSpinorNormClass_append,
    cliffordInvertibleVectorProductSpinorNormClass_cons_self_cons]

@[simp]
theorem cliffordInvertibleVectorProductSpinorNormClass_append_self
    (Q : QuadraticForm R M) (l : List (InvertibleQuadraticVector Q)) :
    cliffordInvertibleVectorProductSpinorNormClass Q (l ++ l) = 1 := by
  rw [cliffordInvertibleVectorProductSpinorNormClass_append]
  simpa [pow_two] using
    cliffordInvertibleVectorProductSpinorNormClass_sq_eq_one Q l

@[simp]
theorem cliffordInvertibleVectorProductSpinorNormClass_append_append_self_append
    (Q : QuadraticForm R M) (l₁ l l₂ : List (InvertibleQuadraticVector Q)) :
    cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l ++ l ++ l₂) =
      cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l₂) := by
  calc
    cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l ++ l ++ l₂) =
        cliffordInvertibleVectorProductSpinorNormClass Q l₁ *
          (cliffordInvertibleVectorProductSpinorNormClass Q l *
            cliffordInvertibleVectorProductSpinorNormClass Q l) *
          cliffordInvertibleVectorProductSpinorNormClass Q l₂ := by
          simp [cliffordInvertibleVectorProductSpinorNormClass_append, mul_assoc]
    _ = cliffordInvertibleVectorProductSpinorNormClass Q l₁ *
          cliffordInvertibleVectorProductSpinorNormClass Q l₂ := by
          rw [show cliffordInvertibleVectorProductSpinorNormClass Q l *
              cliffordInvertibleVectorProductSpinorNormClass Q l = 1 by
            simpa [pow_two] using
              cliffordInvertibleVectorProductSpinorNormClass_sq_eq_one Q l]
          rw [mul_assoc]
          exact congrArg
            (fun x => cliffordInvertibleVectorProductSpinorNormClass Q l₁ * x)
            (one_mul (cliffordInvertibleVectorProductSpinorNormClass Q l₂))
    _ = cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l₂) := by
          rw [cliffordInvertibleVectorProductSpinorNormClass_append]

@[simp]
theorem cliffordInvertibleVectorProductSpinorNormClass_append_append_middle_self_append
    (Q : QuadraticForm R M)
    (l₁ l l₂ l₃ : List (InvertibleQuadraticVector Q)) :
    cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l ++ l₂ ++ l ++ l₃) =
      cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l₂ ++ l₃) := by
  have hperm :
      (l₁ ++ l ++ l₂ ++ l ++ l₃).Perm (l₁ ++ l ++ l ++ l₂ ++ l₃) := by
    simpa [List.append_assoc] using
      List.Perm.append_left (l₁ ++ l)
        (List.Perm.append_right l₃
          (List.perm_append_comm (l₁ := l₂) (l₂ := l)))
  calc
    cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l ++ l₂ ++ l ++ l₃) =
        cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l ++ l ++ l₂ ++ l₃) := by
          exact cliffordInvertibleVectorProductSpinorNormClass_perm Q hperm
    _ = cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l₂ ++ l₃) := by
          simpa [List.append_assoc] using
            cliffordInvertibleVectorProductSpinorNormClass_append_append_self_append
              Q l₁ l (l₂ ++ l₃)

theorem cliffordInvertibleVectorProductSpinorNormClass_eq_of_perm_append_cons_self_cons
    (Q : QuadraticForm R M) {l' : List (InvertibleQuadraticVector Q)}
    (l₁ l₂ : List (InvertibleQuadraticVector Q)) (m : InvertibleQuadraticVector Q)
    (h : l'.Perm (l₁ ++ m :: m :: l₂)) :
    cliffordInvertibleVectorProductSpinorNormClass Q l' =
      cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l₂) := by
  calc
    cliffordInvertibleVectorProductSpinorNormClass Q l' =
        cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ m :: m :: l₂) := by
          exact cliffordInvertibleVectorProductSpinorNormClass_perm Q h
    _ = cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l₂) := by
          exact cliffordInvertibleVectorProductSpinorNormClass_append_cons_self_cons Q l₁ l₂ m

theorem cliffordInvertibleVectorProductSpinorNormClass_eq_of_perm_append_append_middle_self_append
    (Q : QuadraticForm R M) {l' : List (InvertibleQuadraticVector Q)}
    (l₁ l l₂ l₃ : List (InvertibleQuadraticVector Q))
    (h : l'.Perm (l₁ ++ l ++ l₂ ++ l ++ l₃)) :
    cliffordInvertibleVectorProductSpinorNormClass Q l' =
      cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l₂ ++ l₃) := by
  calc
    cliffordInvertibleVectorProductSpinorNormClass Q l' =
        cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l ++ l₂ ++ l ++ l₃) := by
          exact cliffordInvertibleVectorProductSpinorNormClass_perm Q h
    _ = cliffordInvertibleVectorProductSpinorNormClass Q (l₁ ++ l₂ ++ l₃) := by
          exact
            cliffordInvertibleVectorProductSpinorNormClass_append_append_middle_self_append
              Q l₁ l l₂ l₃

end Spinor
