import Spinor.Cl03QuaternionProd
import Mathlib.Data.Matrix.Composition

/-!
  The positive six-dimensional real Bott row.

  This file extends the low-dimensional real Clifford table with the full
  `Cl(6,0) ≃ Mat₄(ℍ)` row.  The construction builds the `6`-generator model as
  a `2 × 2` block matrix algebra over the already-proved `Mat₂(ℍ)` target for
  the first four positive generators.  The fifth and sixth generators use the
  same `Cl(4,0)` volume matrix, first diagonally and then off-diagonally.
-/

namespace Spinor

noncomputable section

open scoped Quaternion
local notation "H" => ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]

/-- The standard negative real 6-dimensional quadratic form on
`(((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)`. -/
noncomputable abbrev realCl06Form :
    QuadraticForm ℝ (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) :=
  CliffordAlgebra.EquivEven.Q' realCl05Form

@[simp] theorem realCl06Form_apply (a b c d e f : ℝ) :
    realCl06Form (((((a, b), c), d), e), f) =
      -(a * a + b * b + c * c + d * d + e * e + f * f) := by
  simp [realCl06Form, realCl05Form]
  ring

/-- The even real Clifford algebra `Cl⁺(0,6)` is isomorphic to `Mat₄(ℂ)`. -/
noncomputable def realEvenCl06EquivComplexMatrix4 :
    CliffordAlgebra.even realCl06Form ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℂ := by
  simpa [realCl06Form] using
    ((CliffordAlgebra.equivEven realCl05Form).symm.trans realCl05EquivComplexMatrix4)

/-- The standard positive real 6-dimensional quadratic form on
`(((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)`. -/
noncomputable abbrev realCl60Form :
    QuadraticForm ℝ (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) :=
  -realCl06Form

@[simp] theorem realCl60Form_apply (a b c d e f : ℝ) :
    realCl60Form (((((a, b), c), d), e), f) =
      a * a + b * b + c * c + d * d + e * e + f * f := by
  simp [realCl60Form]
  ring

/-- The even real Clifford algebra `Cl⁺(6,0)` is isomorphic to `Mat₄(ℂ)`. -/
noncomputable def realEvenCl60EquivComplexMatrix4 :
    CliffordAlgebra.even realCl60Form ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℂ := by
  simpa [realCl60Form] using
    ((CliffordAlgebra.evenEquivEvenNeg (Q := realCl06Form)).symm.trans
      realEvenCl06EquivComplexMatrix4)

/-- The `2 × 2` block target over `Mat₂(ℍ)` used for the full `Cl(6,0)` row. -/
abbrev QuaternionMatrix4Block :=
  Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) H)

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 8000000 in
/-- The six-generator block matrix used for the full `Cl(6,0)` row. -/
def realCl60ToQuaternionMatrix4BlockLin :
    (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) →ₗ[ℝ] QuaternionMatrix4Block where
  toFun v :=
    let p := realCl50ToQuaternionMatrixProdLin v.1
    !![p.1, v.2 • realCl40VolumeMatrix;
       v.2 • realCl40VolumeMatrix, p.2]
  map_add' x y := by
    obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := x
    obtain ⟨⟨⟨⟨⟨g, h⟩, i⟩, j⟩, k⟩, l⟩ := y
    ext r s u v <;> fin_cases r <;> fin_cases s <;> fin_cases u <;> fin_cases v <;>
      simp [realCl50ToQuaternionMatrixProdLin, realCl40ToQuaternionMatrixLin,
        realCl40VolumeMatrix] <;>
      ring
  map_smul' a x := by
    obtain ⟨⟨⟨⟨⟨b, c⟩, d⟩, e⟩, f⟩, g⟩ := x
    ext r s u v <;> fin_cases r <;> fin_cases s <;> fin_cases u <;> fin_cases v <;>
      simp [realCl50ToQuaternionMatrixProdLin, realCl40ToQuaternionMatrixLin,
        realCl40VolumeMatrix]

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 12000000 in
theorem realCl60ToQuaternionMatrix4BlockLin_sq
    (v : (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl60ToQuaternionMatrix4BlockLin v * realCl60ToQuaternionMatrix4BlockLin v =
      algebraMap ℝ QuaternionMatrix4Block (realCl60Form v) := by
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := v
  ext r s u v <;> fin_cases r <;> fin_cases s <;> fin_cases u <;> fin_cases v <;>
    simp [realCl60ToQuaternionMatrix4BlockLin, realCl50ToQuaternionMatrixProdLin,
      realCl40ToQuaternionMatrixLin, realCl40VolumeMatrix, realCl60Form, realCl06Form,
      realCl05Form, Matrix.mul_apply, Matrix.algebraMap_matrix_apply,
      QuaternionAlgebra.mk_mul_mk] <;>
    ring_nf

/-- The explicit block-matrix representation of `Cl(6,0)`. -/
noncomputable def realCl60ToQuaternionMatrix4Block :
    CliffordAlgebra realCl60Form →ₐ[ℝ] QuaternionMatrix4Block :=
  CliffordAlgebra.lift realCl60Form ⟨realCl60ToQuaternionMatrix4BlockLin,
    realCl60ToQuaternionMatrix4BlockLin_sq⟩

@[simp]
theorem realCl60ToQuaternionMatrix4Block_ι
    (v : (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl60ToQuaternionMatrix4Block (CliffordAlgebra.ι realCl60Form v) =
      realCl60ToQuaternionMatrix4BlockLin v := by
  simpa [realCl60ToQuaternionMatrix4Block] using
    (CliffordAlgebra.lift_ι_apply realCl60ToQuaternionMatrix4BlockLin
      realCl60ToQuaternionMatrix4BlockLin_sq v)

/-- Include the first five positive generators of `Cl(6,0)` as a copy of `Cl(5,0)`. -/
noncomputable def realCl50IntoCl60Lin :
    ((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) →ₗ[ℝ] CliffordAlgebra realCl60Form where
  toFun v := CliffordAlgebra.ι realCl60Form (v, 0)
  map_add' x y := by
    simpa using
      (map_add (CliffordAlgebra.ι realCl60Form) (x, (0 : ℝ)) (y, (0 : ℝ)))
  map_smul' a x := by
    simpa using
      (map_smul (CliffordAlgebra.ι realCl60Form) a (x, (0 : ℝ)))

theorem realCl50IntoCl60Lin_sq (v : ((((ℝ × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl50IntoCl60Lin v * realCl50IntoCl60Lin v =
      algebraMap ℝ (CliffordAlgebra realCl60Form) (realCl50Form v) := by
  rw [realCl50IntoCl60Lin, LinearMap.coe_mk, AddHom.coe_mk,
    CliffordAlgebra.ι_sq_scalar]
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := v
  simp [realCl60Form, realCl06Form, realCl50Form, realCl05Form]

/-- The canonical copy of `Cl(5,0)` inside `Cl(6,0)`. -/
noncomputable def realCl50IntoCl60 :
    CliffordAlgebra realCl50Form →ₐ[ℝ] CliffordAlgebra realCl60Form :=
  CliffordAlgebra.lift realCl50Form ⟨realCl50IntoCl60Lin, realCl50IntoCl60Lin_sq⟩

@[simp]
theorem realCl50IntoCl60_ι (v : ((((ℝ × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl50IntoCl60 (CliffordAlgebra.ι realCl50Form v) =
      CliffordAlgebra.ι realCl60Form (v, 0) := by
  simpa [realCl50IntoCl60, realCl50IntoCl60Lin] using
    (CliffordAlgebra.lift_ι_apply realCl50IntoCl60Lin realCl50IntoCl60Lin_sq v)

theorem realCl60ToQuaternionMatrix4Block_realCl50IntoCl60
    (x : CliffordAlgebra realCl50Form) :
    realCl60ToQuaternionMatrix4Block (realCl50IntoCl60 x) =
      !![(realCl50ToQuaternionMatrixProd x).1, 0;
        0, (realCl50ToQuaternionMatrixProd x).2] := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      ext i j u v <;> fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases v <;>
        simp [realCl50IntoCl60, realCl60ToQuaternionMatrix4Block,
          realCl50ToQuaternionMatrixProd, Matrix.algebraMap_matrix_apply]
  | ι v =>
      simp [realCl60ToQuaternionMatrix4Block_ι, realCl50ToQuaternionMatrixProd_ι,
        realCl60ToQuaternionMatrix4BlockLin, realCl50ToQuaternionMatrixProdLin]
  | add x y hx hy =>
      simp [map_add, hx, hy]
  | mul x y hx hy =>
      simp [map_mul, hx, hy]

/-- The sixth positive generator of `Cl(6,0)`. -/
noncomputable def realCl60SixthGenerator : CliffordAlgebra realCl60Form :=
  CliffordAlgebra.ι realCl60Form
    ((0 : ((((ℝ × ℝ) × ℝ) × ℝ) × ℝ)), (1 : ℝ))

@[simp]
theorem realCl60ToQuaternionMatrix4Block_sixthGenerator :
    realCl60ToQuaternionMatrix4Block realCl60SixthGenerator =
      !![0, realCl40VolumeMatrix; realCl40VolumeMatrix, 0] := by
  simp [realCl60SixthGenerator, realCl60ToQuaternionMatrix4BlockLin]

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 8000000 in
theorem realCl60ToQuaternionMatrix4Block_surjective :
    Function.Surjective realCl60ToQuaternionMatrix4Block := by
  intro A
  rcases realCl50ToQuaternionMatrixProd_surjective (A 0 0, A 1 1) with ⟨x, hx⟩
  let Y : Matrix (Fin 2) (Fin 2) H × Matrix (Fin 2) (Fin 2) H :=
    (realCl40VolumeMatrix * A 1 0, realCl40VolumeMatrix * A 0 1)
  rcases realCl50ToQuaternionMatrixProd_surjective Y with ⟨y, hy⟩
  refine ⟨realCl50IntoCl60 x + realCl60SixthGenerator * realCl50IntoCl60 y, ?_⟩
  rw [map_add, map_mul, realCl60ToQuaternionMatrix4Block_realCl50IntoCl60 x,
    realCl60ToQuaternionMatrix4Block_realCl50IntoCl60 y,
    realCl60ToQuaternionMatrix4Block_sixthGenerator, hx, hy]
  have h10 : realCl40VolumeMatrix * (realCl40VolumeMatrix * A 1 0) = A 1 0 := by
    rw [← mul_assoc, realCl40VolumeMatrix_sq, one_mul]
  have h01 : realCl40VolumeMatrix * (realCl40VolumeMatrix * A 0 1) = A 0 1 := by
    rw [← mul_assoc, realCl40VolumeMatrix_sq, one_mul]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Y, h10, h01]

theorem realCl60Clifford_finrank :
    Module.finrank ℝ (CliffordAlgebra realCl60Form) = 64 := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hfin :
      Module.finrank ℝ (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) = 6 := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
      Module.finrank_prod, Module.finrank_prod]
    norm_num
  calc
    Module.finrank ℝ (CliffordAlgebra realCl60Form) =
        Module.finrank ℝ (ExteriorAlgebra ℝ (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) := by
      exact LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior realCl60Form)
    _ = 2 ^ Module.finrank ℝ (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) := by
      exact ExteriorAlgebra.finrank_eq_two_pow (K := ℝ)
    _ = 64 := by
      rw [hfin]
      norm_num

theorem realCl60QuaternionMatrix4Block_finrank :
    Module.finrank ℝ QuaternionMatrix4Block = 64 := by
  rw [Module.finrank_matrix]
  norm_num [realCl40QuaternionMatrix_finrank]

theorem realCl60ToQuaternionMatrix4Block_injective :
    Function.Injective realCl60ToQuaternionMatrix4Block := by
  have hcl_succ : Module.finrank ℝ (CliffordAlgebra realCl60Form) = Nat.succ 63 := by
    simpa using realCl60Clifford_finrank
  letI : FiniteDimensional ℝ (CliffordAlgebra realCl60Form) :=
    FiniteDimensional.of_finrank_eq_succ hcl_succ
  have hdim : Module.finrank ℝ (CliffordAlgebra realCl60Form) =
      Module.finrank ℝ QuaternionMatrix4Block := by
    rw [realCl60Clifford_finrank, realCl60QuaternionMatrix4Block_finrank]
  simpa using
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := realCl60ToQuaternionMatrix4Block.toLinearMap) hdim).mpr
      realCl60ToQuaternionMatrix4Block_surjective)

/-- The real Clifford algebra `Cl(6,0)` is the full `2 × 2` block matrix algebra over
`Mat₂(ℍ)`. -/
noncomputable def realCl60EquivQuaternionMatrix4Block :
    CliffordAlgebra realCl60Form ≃ₐ[ℝ] QuaternionMatrix4Block :=
  AlgEquiv.ofBijective realCl60ToQuaternionMatrix4Block
    ⟨realCl60ToQuaternionMatrix4Block_injective,
      realCl60ToQuaternionMatrix4Block_surjective⟩

@[simp]
theorem realCl60EquivQuaternionMatrix4Block_apply_ι
    (v : (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl60EquivQuaternionMatrix4Block (CliffordAlgebra.ι realCl60Form v) =
      realCl60ToQuaternionMatrix4BlockLin v := by
  simp [realCl60EquivQuaternionMatrix4Block]

/-- The real Clifford algebra `Cl(6,0)` is the full `4 × 4` quaternionic matrix algebra. -/
noncomputable def realCl60EquivQuaternionMatrix4 :
    CliffordAlgebra realCl60Form ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) H :=
  realCl60EquivQuaternionMatrix4Block.trans
    ((Matrix.compAlgEquiv (Fin 2) (Fin 2) H ℝ).trans
      (Matrix.reindexAlgEquiv ℝ H (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2))))

namespace RealClassification

/-- Canonical quadratic form for `Cl(0,6)` and its even algebra in the real-classification
namespace. -/
noncomputable abbrev Q_0_6 :
    QuadraticForm ℝ (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) :=
  realCl06Form

/-- Canonical even real-classification entry: `Cl⁺(0,6) ≃ Mat₄(ℂ)`. -/
noncomputable def cl_0_6_even_equivComplexMatrix4 :
    CliffordAlgebra.even Q_0_6 ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℂ := by
  simpa [Q_0_6] using realEvenCl06EquivComplexMatrix4

/-- Canonical quadratic form for `Cl(6,0)` and its even algebra in the real-classification
namespace. -/
noncomputable abbrev Q_6_0 :
    QuadraticForm ℝ (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) :=
  realCl60Form

/-- Canonical even real-classification entry: `Cl⁺(6,0) ≃ Mat₄(ℂ)`. -/
noncomputable def cl_6_0_even_equivComplexMatrix4 :
    CliffordAlgebra.even Q_6_0 ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℂ := by
  simpa [Q_6_0] using realEvenCl60EquivComplexMatrix4

/-- Canonical real-classification entry: `Cl(6,0) ≃ Mat₄(ℍ)`. -/
noncomputable def cl_6_0_equivQuaternionMatrix4 :
    CliffordAlgebra Q_6_0 ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) H := by
  simpa [Q_6_0] using realCl60EquivQuaternionMatrix4

end RealClassification

end

end Spinor
