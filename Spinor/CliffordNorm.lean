/-
  Clifford norm formulas for products of vectors.

  This module gives the global Clifford-algebra calculation behind the
  reflection-product form of the spinor norm. It also packages those products as
  elements of Mathlib's `lipschitzGroup` and proves factorization existence for
  every Lipschitz element when `2` is invertible. The scalar Clifford norm formula
  then proves independence of the chosen Lipschitz vector factorization. This does
  not assert descent to a full orthogonal-group spinor-norm homomorphism.
-/

import Spinor.OrthogonalAction
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Clifford norm formulas

For a list of vectors, the Clifford conjugation norm of the product of their
`ι`-images is the scalar product of the signed quadratic values. For a product
of invertible vectors, this scalar is also packaged as a unit and as its
square-class quotient, and as a Lipschitz-group element from a chosen vector
product. When `2` is invertible, every Mathlib `lipschitzGroup` element has such
a vector-product representative, and the resulting square class is independent of
that representative. These declarations provide a global
Clifford/Lipschitz substrate for later spinor-norm developments without claiming
an orthogonal-group spinor-norm API.

## Main declarations

* `Spinor.cliffordVectorProduct`
* `Spinor.cliffordVectorProductNormScalar`
* `Spinor.star_cliffordVectorProduct_mul_cliffordVectorProduct`
* `Spinor.cliffordInvertibleVectorProductNormUnit`
* `Spinor.cliffordInvertibleVectorLipschitz`
* `Spinor.cliffordInvertibleVectorProductLipschitz`
* `Spinor.exists_cliffordInvertibleVectorProductLipschitz_eq`
* `Spinor.cliffordInvertibleVectorProductSpinorNormClass`
* `Spinor.cliffordInvertibleVectorProductSpinorNormClass_perm`
* `Spinor.LipschitzVectorFactorization.mul`
* `Spinor.LipschitzVectorFactorization.normUnit_mul`
* `Spinor.LipschitzVectorFactorization.spinorNormClass_mul`
* `Spinor.lipschitzVectorFactorization`
* `Spinor.chosenLipschitzSpinorNormClass`
* `Spinor.LipschitzSpinorNormClassFactorizationIndependent`
* `Spinor.lipschitzVectorFactorization_normUnit_eq_of_factorizations`
* `Spinor.lipschitzVectorFactorization_spinorNormClass_eq_of_factorizations`
* `Spinor.lipschitzSpinorNormClassFactorizationIndependent`
* `Spinor.lipschitzSpinorNormClassHom`
* `Spinor.lipschitzSpinorNormClassHomOfFactorizationIndependent`
* `Spinor.chosenLipschitzNormUnit_eq_sq_of_coe_eq_algebraMap_unit`
* `Spinor.lipschitzSpinorNormClassHom_eq_one_of_coe_eq_algebraMap_unit`
* `Spinor.exists_lipschitzVectorFactorization_mul_chosenSpinorNormClass_eq`
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
  convert star_cliffordInvertibleVectorProductLipschitz_mul_self (Q := Q) [m] using 1 <;>
    simp [cliffordInvertibleVectorProductLipschitz, cliffordInvertibleVectorProductNormUnit]

/-- The vector factor representing the inverse of an invertible vector generator. -/
noncomputable def invertibleQuadraticVectorInvFactor (Q : QuadraticForm R M)
    (m : InvertibleQuadraticVector Q) : InvertibleQuadraticVector Q :=
  ⟨((m.2.unit⁻¹ : Rˣ) : R) • m.1, by
    rw [QuadraticMap.map_smul]
    change IsUnit
      ((((m.2.unit⁻¹ : Rˣ) : R) * ((m.2.unit⁻¹ : Rˣ) : R)) * Q m.1)
    exact ((m.2.unit⁻¹).isUnit.mul (m.2.unit⁻¹).isUnit).mul m.2⟩

@[simp]
theorem invertibleQuadraticVectorInvFactor_val (Q : QuadraticForm R M)
    (m : InvertibleQuadraticVector Q) :
    (invertibleQuadraticVectorInvFactor Q m).1 =
      ((m.2.unit⁻¹ : Rˣ) : R) • m.1 := rfl

/-- A vector inverse in the Lipschitz group is again represented by a vector. -/
theorem cliffordInvertibleVectorLipschitz_invFactor_eq_inv
    (Q : QuadraticForm R M) (m : InvertibleQuadraticVector Q) :
    cliffordInvertibleVectorLipschitz Q (invertibleQuadraticVectorInvFactor Q m) =
      (cliffordInvertibleVectorLipschitz Q m)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  change CliffordAlgebra.ι Q (((m.2.unit⁻¹ : Rˣ) : R) • m.1) =
    (((cliffordInvertibleVectorUnit Q m)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  have hsQ : ((m.2.unit⁻¹ : Rˣ) : R) * Q m.1 = 1 := by
    simp
  have hmul :
      CliffordAlgebra.ι Q (((m.2.unit⁻¹ : Rˣ) : R) • m.1) *
          CliffordAlgebra.ι Q m.1 = 1 := by
    rw [map_smul, smul_mul_assoc, CliffordAlgebra.ι_sq_scalar, Algebra.smul_def,
      ← map_mul, hsQ, map_one]
  let u := cliffordInvertibleVectorUnit Q m
  have huval : ((u : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q m.1 := by
    exact coe_cliffordInvertibleVectorUnit Q m
  have hu_val_inv : ((u : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
      (((u)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = 1 := by
    simp [u]
  calc
    CliffordAlgebra.ι Q (((m.2.unit⁻¹ : Rˣ) : R) • m.1) =
        CliffordAlgebra.ι Q (((m.2.unit⁻¹ : Rˣ) : R) • m.1) * 1 := by
          rw [mul_one]
    _ = CliffordAlgebra.ι Q (((m.2.unit⁻¹ : Rˣ) : R) • m.1) *
          (((u : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
            (((u)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := by
          rw [hu_val_inv]
    _ = (CliffordAlgebra.ι Q (((m.2.unit⁻¹ : Rˣ) : R) • m.1) *
          ((u : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) *
            (((u)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
          rw [mul_assoc]
    _ = (CliffordAlgebra.ι Q (((m.2.unit⁻¹ : Rˣ) : R) • m.1) *
          CliffordAlgebra.ι Q m.1) *
            (((u)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
          rw [huval]
    _ = 1 * (((u)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
          rw [hmul]
    _ = (((u)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
          rw [one_mul]

/--
Every Mathlib Lipschitz-group element is represented by a finite product of invertible
quadratic vectors, provided `2` is invertible in the coefficient ring.

This follows from Mathlib's definition of `lipschitzGroup` as a subgroup closure of the
invertible vector generators. It is still a factorization statement, not an independence or
descent theorem for an orthogonal-group spinor norm.
-/
theorem exists_cliffordInvertibleVectorProductLipschitz_eq
    [Invertible (2 : R)] (Q : QuadraticForm R M) (x : lipschitzGroup Q) :
    ∃ l : List (InvertibleQuadraticVector Q),
      cliffordInvertibleVectorProductLipschitz Q l = x := by
  let s : Set (CliffordAlgebra Q)ˣ := ((↑) ⁻¹' Set.range (CliffordAlgebra.ι Q))
  have hx : (x : (CliffordAlgebra Q)ˣ) ∈ Subgroup.closure s := by
    simp [s, lipschitzGroup]
  have hfac : ∃ l : List (InvertibleQuadraticVector Q),
      ((cliffordInvertibleVectorProductLipschitz Q l : lipschitzGroup Q) :
        (CliffordAlgebra Q)ˣ) = (x : (CliffordAlgebra Q)ˣ) := by
    refine Subgroup.closure_induction'' (s := s)
      (p := fun u _ => ∃ l : List (InvertibleQuadraticVector Q),
        ((cliffordInvertibleVectorProductLipschitz Q l : lipschitzGroup Q) :
          (CliffordAlgebra Q)ˣ) = u) ?mem ?inv_mem ?one ?mul hx
    · intro u hu
      obtain ⟨m, hm⟩ := hu
      have hunit_iota : IsUnit (CliffordAlgebra.ι Q m) := by
        rw [hm]
        exact u.isUnit
      have hQ : IsUnit (Q m) := CliffordAlgebra.isUnit_of_isUnit_ι (Q := Q) hunit_iota
      let v : InvertibleQuadraticVector Q := ⟨m, hQ⟩
      refine ⟨[v], ?_⟩
      apply Units.ext
      simpa [cliffordInvertibleVectorProductLipschitz, v] using hm
    · intro u hu
      obtain ⟨m, hm⟩ := hu
      have hunit_iota : IsUnit (CliffordAlgebra.ι Q m) := by
        rw [hm]
        exact u.isUnit
      have hQ : IsUnit (Q m) := CliffordAlgebra.isUnit_of_isUnit_ι (Q := Q) hunit_iota
      let v : InvertibleQuadraticVector Q := ⟨m, hQ⟩
      have hvu : ((cliffordInvertibleVectorLipschitz Q v : lipschitzGroup Q) :
          (CliffordAlgebra Q)ˣ) = u := by
        apply Units.ext
        simpa [v] using hm
      refine ⟨[invertibleQuadraticVectorInvFactor Q v], ?_⟩
      have hInv := cliffordInvertibleVectorLipschitz_invFactor_eq_inv (Q := Q) v
      have hInvUnits := congrArg
        (fun y : lipschitzGroup Q => ((y : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ)) hInv
      simpa [cliffordInvertibleVectorProductLipschitz, hvu] using hInvUnits
    · exact ⟨[], rfl⟩
    · intro u v hu hv ihu ihv
      obtain ⟨lu, hlu⟩ := ihu
      obtain ⟨lv, hlv⟩ := ihv
      refine ⟨lu ++ lv, ?_⟩
      rw [cliffordInvertibleVectorProductLipschitz_append]
      change ((cliffordInvertibleVectorProductLipschitz Q lu : lipschitzGroup Q) :
          (CliffordAlgebra Q)ˣ) *
        ((cliffordInvertibleVectorProductLipschitz Q lv : lipschitzGroup Q) :
          (CliffordAlgebra Q)ˣ) = u * v
      rw [hlu, hlv]
  obtain ⟨l, hl⟩ := hfac
  exact ⟨l, Subtype.ext hl⟩

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

This is the group-level replacement for bare vector lists. It stores the factorization data;
later the norm formula proves the norm unit and square class are independent of which
factorization is chosen for a fixed Lipschitz-group element.
-/
structure LipschitzVectorFactorization (Q : QuadraticForm R M) (x : lipschitzGroup Q) where
  factors : List (InvertibleQuadraticVector Q)
  product_eq : cliffordInvertibleVectorProductLipschitz Q factors = x

namespace LipschitzVectorFactorization

variable {Q : QuadraticForm R M}

/-- The empty vector product as a factorization of the identity Lipschitz element. -/
def one (Q : QuadraticForm R M) :
    LipschitzVectorFactorization Q (1 : lipschitzGroup Q) where
  factors := []
  product_eq := by simp

/-- Concatenating factor lists gives a factorization of the product. -/
def mul {x y : lipschitzGroup Q}
    (F : LipschitzVectorFactorization Q x) (G : LipschitzVectorFactorization Q y) :
    LipschitzVectorFactorization Q (x * y) where
  factors := F.factors ++ G.factors
  product_eq := by
    rw [cliffordInvertibleVectorProductLipschitz_append, F.product_eq, G.product_eq]

/-- The Clifford norm unit attached to a chosen Lipschitz vector factorization. -/
noncomputable def normUnit {x : lipschitzGroup Q}
    (F : LipschitzVectorFactorization Q x) : Rˣ :=
  cliffordInvertibleVectorProductNormUnit Q F.factors

@[simp]
theorem normUnit_one (Q : QuadraticForm R M) :
    (one (Q := Q)).normUnit = 1 := rfl

@[simp]
theorem normUnit_mul {x y : lipschitzGroup Q}
    (F : LipschitzVectorFactorization Q x) (G : LipschitzVectorFactorization Q y) :
    (F.mul G).normUnit = F.normUnit * G.normUnit := by
  simp [mul, normUnit]

/-- The square-class spinor norm attached to a chosen Lipschitz vector factorization. -/
noncomputable def spinorNormClass {x : lipschitzGroup Q}
    (F : LipschitzVectorFactorization Q x) :
    Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2) :=
  cliffordInvertibleVectorProductSpinorNormClass Q F.factors

@[simp]
theorem spinorNormClass_one (Q : QuadraticForm R M) :
    (one (Q := Q)).spinorNormClass = 1 := rfl

@[simp]
theorem spinorNormClass_mul {x y : lipschitzGroup Q}
    (F : LipschitzVectorFactorization Q x) (G : LipschitzVectorFactorization Q y) :
    (F.mul G).spinorNormClass = F.spinorNormClass * G.spinorNormClass := by
  simp [mul, spinorNormClass]

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
      algebraMap R (CliffordAlgebra Q) (F.normUnit : R) := by
  have hx :
      (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        (((cliffordInvertibleVectorProductLipschitz Q F.factors : lipschitzGroup Q) :
          (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
    exact congrArg
      (fun y : lipschitzGroup Q => (((y : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q)) F.product_eq.symm
  rw [hx]
  simpa [normUnit] using
    star_cliffordInvertibleVectorProductLipschitz_mul_self (Q := Q) F.factors

end LipschitzVectorFactorization

/-- A noncomputable chosen vector factorization of a Lipschitz-group element. -/
noncomputable def lipschitzVectorFactorization [Invertible (2 : R)]
    (Q : QuadraticForm R M) (x : lipschitzGroup Q) :
    LipschitzVectorFactorization Q x :=
  let h := exists_cliffordInvertibleVectorProductLipschitz_eq (Q := Q) x
  ⟨Classical.choose h, Classical.choose_spec h⟩

/-- Every Lipschitz-group element has a vector factorization when `2` is invertible. -/
theorem exists_lipschitzVectorFactorization [Invertible (2 : R)]
    (Q : QuadraticForm R M) (x : lipschitzGroup Q) :
    Nonempty (LipschitzVectorFactorization Q x) :=
  ⟨lipschitzVectorFactorization Q x⟩

/-- There is a factorization of the identity whose square-class spinor norm is trivial. -/
theorem exists_lipschitzVectorFactorization_one_spinorNormClass_eq_one
    (Q : QuadraticForm R M) :
    ∃ F : LipschitzVectorFactorization Q (1 : lipschitzGroup Q),
      F.spinorNormClass = 1 :=
  ⟨LipschitzVectorFactorization.one (Q := Q), by simp⟩

/-- Given factorizations of two Lipschitz elements, there is a product factorization whose
square-class spinor norm is the product of the two square classes. -/
theorem exists_lipschitzVectorFactorization_mul_spinorNormClass_eq
    {Q : QuadraticForm R M} {x y : lipschitzGroup Q}
    (F : LipschitzVectorFactorization Q x) (G : LipschitzVectorFactorization Q y) :
    ∃ H : LipschitzVectorFactorization Q (x * y),
      H.spinorNormClass = F.spinorNormClass * G.spinorNormClass :=
  ⟨F.mul G, by simp⟩

/--
The Clifford norm unit attached to the repository's noncomputable chosen Lipschitz
vector factorization.

This is intentionally a chosen-factorization API. The theorem
`lipschitzVectorFactorization_normUnit_eq_of_factorizations` below proves that different
choices nevertheless give the same norm unit.
-/
noncomputable def chosenLipschitzNormUnit [Invertible (2 : R)]
    (Q : QuadraticForm R M) (x : lipschitzGroup Q) : Rˣ :=
  (lipschitzVectorFactorization Q x).normUnit

/--
The square-class attached to the repository's noncomputable chosen Lipschitz vector
factorization.

This is not a descended orthogonal-group spinor norm: it records the square-class of the
particular vector product selected by `lipschitzVectorFactorization`. The theorem
`lipschitzVectorFactorization_spinorNormClass_eq_of_factorizations` below proves that this
choice is independent on the Lipschitz group.
-/
noncomputable def chosenLipschitzSpinorNormClass [Invertible (2 : R)]
    (Q : QuadraticForm R M) (x : lipschitzGroup Q) :
    Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2) :=
  (lipschitzVectorFactorization Q x).spinorNormClass

/--
The factorization-independence theorem needed to turn the noncomputable chosen
Lipschitz square-class value into a genuine monoid-level spinor norm on the
Lipschitz group.

This structure records the exact Cartan--Dieudonne-style obligation: any two Lipschitz vector
factorizations of the same Lipschitz-group element have the same square class. The theorem
`lipschitzSpinorNormClassFactorizationIndependent` below discharges this obligation globally.
-/
structure LipschitzSpinorNormClassFactorizationIndependent [Invertible (2 : R)]
    (Q : QuadraticForm R M) : Prop where
  eq_of_factorizations : ∀ {x : lipschitzGroup Q}
    (F G : LipschitzVectorFactorization Q x), F.spinorNormClass = G.spinorNormClass

/--
Two Lipschitz vector factorizations of the same Lipschitz-group element have the same
Clifford norm unit.

The proof compares the two scalar Clifford norm formulas for the common underlying
Lipschitz element and uses injectivity of the scalar embedding into the Clifford algebra.
-/
theorem lipschitzVectorFactorization_normUnit_eq_of_factorizations
    [Invertible (2 : R)] (Q : QuadraticForm R M) {x : lipschitzGroup Q}
    (F G : LipschitzVectorFactorization Q x) :
    F.normUnit = G.normUnit := by
  apply Units.ext
  apply cliffordAlgebraMap_injective (Q := Q)
  rw [← F.star_mul_self_eq_algebraMap_normUnit, ← G.star_mul_self_eq_algebraMap_normUnit]

/--
Two Lipschitz vector factorizations of the same Lipschitz-group element have the same
spinor-norm square class.
-/
theorem lipschitzVectorFactorization_spinorNormClass_eq_of_factorizations
    [Invertible (2 : R)] (Q : QuadraticForm R M) {x : lipschitzGroup Q}
    (F G : LipschitzVectorFactorization Q x) :
    F.spinorNormClass = G.spinorNormClass := by
  change ((F.normUnit : Rˣ) :
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2)) =
    ((G.normUnit : Rˣ) :
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2))
  rw [lipschitzVectorFactorization_normUnit_eq_of_factorizations Q F G]

/--
Global factorization independence for the Lipschitz square-class spinor norm.

This discharges the formerly separate factorization-independence obligation: the square
class is determined by the Lipschitz-group element, not by the chosen invertible-vector
factorization.
-/
theorem lipschitzSpinorNormClassFactorizationIndependent
    [Invertible (2 : R)] (Q : QuadraticForm R M) :
    LipschitzSpinorNormClassFactorizationIndependent Q where
  eq_of_factorizations := lipschitzVectorFactorization_spinorNormClass_eq_of_factorizations Q

/-- Under factorization independence, the chosen Lipschitz square class is trivial at `1`. -/
theorem chosenLipschitzSpinorNormClass_one_of_factorizationIndependent
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (h : LipschitzSpinorNormClassFactorizationIndependent Q) :
    chosenLipschitzSpinorNormClass Q (1 : lipschitzGroup Q) = 1 := by
  calc
    chosenLipschitzSpinorNormClass Q (1 : lipschitzGroup Q) =
        (LipschitzVectorFactorization.one (Q := Q)).spinorNormClass := by
          exact h.eq_of_factorizations
            (lipschitzVectorFactorization Q (1 : lipschitzGroup Q))
            (LipschitzVectorFactorization.one (Q := Q))
    _ = 1 := by simp

/-- Under factorization independence, the chosen Lipschitz square class is multiplicative. -/
theorem chosenLipschitzSpinorNormClass_mul_of_factorizationIndependent
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (h : LipschitzSpinorNormClassFactorizationIndependent Q) (x y : lipschitzGroup Q) :
    chosenLipschitzSpinorNormClass Q (x * y) =
      chosenLipschitzSpinorNormClass Q x * chosenLipschitzSpinorNormClass Q y := by
  calc
    chosenLipschitzSpinorNormClass Q (x * y) =
        ((lipschitzVectorFactorization Q x).mul
          (lipschitzVectorFactorization Q y)).spinorNormClass := by
          exact h.eq_of_factorizations (lipschitzVectorFactorization Q (x * y))
            ((lipschitzVectorFactorization Q x).mul (lipschitzVectorFactorization Q y))
    _ = chosenLipschitzSpinorNormClass Q x * chosenLipschitzSpinorNormClass Q y := by
          simp [chosenLipschitzSpinorNormClass]

/--
Under factorization independence, the chosen Lipschitz square-class API is a monoid
homomorphism on the full Lipschitz group.

This is still conditional: the input hypothesis is exactly the missing global
factorization-independence theorem for Lipschitz vector products.
-/
noncomputable def lipschitzSpinorNormClassHomOfFactorizationIndependent
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (h : LipschitzSpinorNormClassFactorizationIndependent Q) :
    lipschitzGroup Q →*
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2) where
  toFun := chosenLipschitzSpinorNormClass Q
  map_one' := chosenLipschitzSpinorNormClass_one_of_factorizationIndependent Q h
  map_mul' := chosenLipschitzSpinorNormClass_mul_of_factorizationIndependent Q h

@[simp]
theorem lipschitzSpinorNormClassHomOfFactorizationIndependent_apply
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (h : LipschitzSpinorNormClassFactorizationIndependent Q) (x : lipschitzGroup Q) :
    lipschitzSpinorNormClassHomOfFactorizationIndependent Q h x =
      chosenLipschitzSpinorNormClass Q x := rfl

/--
The global Lipschitz-group spinor-norm square-class homomorphism obtained from the
factorization-independence theorem.
-/
noncomputable def lipschitzSpinorNormClassHom [Invertible (2 : R)]
    (Q : QuadraticForm R M) :
    lipschitzGroup Q →*
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2) :=
  lipschitzSpinorNormClassHomOfFactorizationIndependent Q
    (lipschitzSpinorNormClassFactorizationIndependent Q)

@[simp]
theorem lipschitzSpinorNormClassHom_apply [Invertible (2 : R)]
    (Q : QuadraticForm R M) (x : lipschitzGroup Q) :
    lipschitzSpinorNormClassHom Q x = chosenLipschitzSpinorNormClass Q x := rfl

/-- For any two Lipschitz elements, the chosen square classes can be realized by a
factorization of their product whose square class is the product of the chosen values. This
is still a factorization-level statement, not a proof that the repository's noncomputable
chosen value on `x * y` is multiplicative. -/
theorem exists_lipschitzVectorFactorization_mul_chosenSpinorNormClass_eq
    [Invertible (2 : R)] (Q : QuadraticForm R M) (x y : lipschitzGroup Q) :
    ∃ H : LipschitzVectorFactorization Q (x * y),
      H.spinorNormClass =
        chosenLipschitzSpinorNormClass Q x * chosenLipschitzSpinorNormClass Q y := by
  refine ⟨(lipschitzVectorFactorization Q x).mul (lipschitzVectorFactorization Q y), ?_⟩
  simp [chosenLipschitzSpinorNormClass]

@[simp]
theorem chosenLipschitzSpinorNormClass_sq_eq_one [Invertible (2 : R)]
    (Q : QuadraticForm R M) (x : lipschitzGroup Q) :
    chosenLipschitzSpinorNormClass Q x ^ 2 = 1 :=
  (lipschitzVectorFactorization Q x).spinorNormClass_sq_eq_one

/-- Norm formula for the repository's noncomputable chosen Lipschitz vector factorization. -/
theorem star_mul_self_eq_algebraMap_chosenLipschitzNormUnit [Invertible (2 : R)]
    (Q : QuadraticForm R M) (x : lipschitzGroup Q) :
    star (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (chosenLipschitzNormUnit Q x : R) :=
  (lipschitzVectorFactorization Q x).star_mul_self_eq_algebraMap_normUnit

/--
If a Lipschitz element is a scalar unit in the Clifford algebra, then its chosen Clifford
norm unit is the square of that scalar unit.
-/
theorem chosenLipschitzNormUnit_eq_sq_of_coe_eq_algebraMap_unit [Invertible (2 : R)]
    (Q : QuadraticForm R M) (x : lipschitzGroup Q) (u : Rˣ)
    (hx : (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (u : R)) :
    chosenLipschitzNormUnit Q x = u ^ 2 := by
  apply Units.ext
  apply cliffordAlgebraMap_injective (Q := Q)
  calc
    algebraMap R (CliffordAlgebra Q) ((chosenLipschitzNormUnit Q x : Rˣ) : R) =
        star (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
          (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
          rw [← star_mul_self_eq_algebraMap_chosenLipschitzNormUnit (Q := Q) x]
    _ = star (algebraMap R (CliffordAlgebra Q) (u : R)) *
        algebraMap R (CliffordAlgebra Q) (u : R) := by
          rw [hx]
    _ = algebraMap R (CliffordAlgebra Q) (((u ^ 2 : Rˣ) : R)) := by
          simp [pow_two, CliffordAlgebra.star_algebraMap]

/--
Scalar-unit Lipschitz elements have trivial square-class spinor norm.

This is the concrete scalar-kernel calculation used by the image-level descent API: once a
kernel element is known to be scalar, its norm is a square.
-/
theorem chosenLipschitzSpinorNormClass_eq_one_of_coe_eq_algebraMap_unit
    [Invertible (2 : R)] (Q : QuadraticForm R M) (x : lipschitzGroup Q) (u : Rˣ)
    (hx : (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (u : R)) :
    chosenLipschitzSpinorNormClass Q x = 1 := by
  change ((chosenLipschitzNormUnit Q x : Rˣ) :
      Rˣ ⧸ MonoidHom.range (powMonoidHom (α := Rˣ) 2)) = 1
  rw [chosenLipschitzNormUnit_eq_sq_of_coe_eq_algebraMap_unit Q x u hx]
  rw [QuotientGroup.eq_one_iff]
  exact ⟨u, rfl⟩

/-- The factorization-independent Lipschitz-group spinor-norm hom is trivial on scalar units. -/
theorem lipschitzSpinorNormClassHomOfFactorizationIndependent_eq_one_of_coe_eq_algebraMap_unit
    [Invertible (2 : R)] (Q : QuadraticForm R M)
    (h : LipschitzSpinorNormClassFactorizationIndependent Q) (x : lipschitzGroup Q) (u : Rˣ)
    (hx : (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (u : R)) :
    lipschitzSpinorNormClassHomOfFactorizationIndependent Q h x = 1 := by
  rw [lipschitzSpinorNormClassHomOfFactorizationIndependent_apply]
  exact chosenLipschitzSpinorNormClass_eq_one_of_coe_eq_algebraMap_unit Q x u hx

/-- The global Lipschitz-group spinor-norm hom is trivial on scalar units. -/
theorem lipschitzSpinorNormClassHom_eq_one_of_coe_eq_algebraMap_unit
    [Invertible (2 : R)] (Q : QuadraticForm R M) (x : lipschitzGroup Q) (u : Rˣ)
    (hx : (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (u : R)) :
    lipschitzSpinorNormClassHom Q x = 1 := by
  rw [lipschitzSpinorNormClassHom_apply]
  exact chosenLipschitzSpinorNormClass_eq_one_of_coe_eq_algebraMap_unit Q x u hx

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
