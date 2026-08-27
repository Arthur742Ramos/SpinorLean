import Spinor.Cl60QuaternionMatrix

/-!
  The negative seven-dimensional real Bott row.

  This file extends the explicit real Clifford table with
  `Cl(0,7) ≃ Mat₈(ℝ) × Mat₈(ℝ)`.  The first six generators use the
  already-proved `Cl(0,6) ≃ Mat₈(ℝ)` block model, and the seventh generator is
  represented by the `Cl(0,6)` volume matrix with opposite signs in the two
  product factors.
-/

namespace Spinor

noncomputable section

/-- The standard negative real 7-dimensional quadratic form on
`((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)`. -/
noncomputable abbrev realCl07Form :
    QuadraticForm ℝ ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) :=
  CliffordAlgebra.EquivEven.Q' realCl06Form

@[simp] theorem realCl07Form_apply (a b c d e f g : ℝ) :
    realCl07Form ((((((a, b), c), d), e), f), g) =
      -(a * a + b * b + c * c + d * d + e * e + f * f + g * g) := by
  simp [realCl07Form, realCl06Form, realCl05Form]
  ring

/-- The even real Clifford algebra `Cl⁺(0,7)` is isomorphic to `Mat₈(ℝ)`. -/
noncomputable def realEvenCl07EquivRealMatrix8 :
    CliffordAlgebra.even realCl07Form ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ := by
  simpa [realCl07Form] using
    ((CliffordAlgebra.equivEven realCl06Form).symm.trans realCl06EquivRealMatrix8)

/-- The `Cl(0,6)` volume matrix in the explicit real `8 × 8` block model. It
squares to `-1` and anticommutes with the six `Cl(0,6)` generators, so it
supplies the two irreducible extensions of the `Cl(0,6)` module to `Cl(0,7)`. -/
def realCl06VolumeBlock : RealMatrix8Block :=
  !![0, -realCl06ConjMatrixP;
     -realCl06ConjMatrixP, 0]

set_option linter.unnecessarySeqFocus false in
@[simp]
theorem realCl06VolumeBlock_sq :
    realCl06VolumeBlock * realCl06VolumeBlock = -1 := by
  ext i j u v <;> fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases v <;>
    simp [realCl06VolumeBlock, realCl06ConjMatrixP, Matrix.mul_apply,
      Fin.sum_univ_two]

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 12000000 in
theorem realCl06ToRealMatrix8BlockLin_mul_volume_add_volume_mul
    (v : (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl06ToRealMatrix8BlockLin v * realCl06VolumeBlock +
        realCl06VolumeBlock * realCl06ToRealMatrix8BlockLin v = 0 := by
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := v
  ext i j u w <;> fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases w <;>
    simp [realCl06ToRealMatrix8BlockLin, complexLinearRealBlock4, complexMatrix4Re,
      complexMatrix4Im, realCl06SixthBlock, realCl06ConjMatrixP, realCl05ToComplexMatrix4Mat,
      realCl06VolumeBlock, Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul, dotProduct,
      Complex.mul_re, Complex.mul_im]

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 8000000 in
theorem realCl06ToRealMatrix8BlockLin_add_smul_volume_sq
    (v : (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) (r : ℝ) :
    (realCl06ToRealMatrix8BlockLin v + r • realCl06VolumeBlock) *
        (realCl06ToRealMatrix8BlockLin v + r • realCl06VolumeBlock) =
      algebraMap ℝ RealMatrix8Block (realCl06Form v - r * r) := by
  let A := realCl06ToRealMatrix8BlockLin v
  let W := realCl06VolumeBlock
  have hsq : A * A = algebraMap ℝ RealMatrix8Block (realCl06Form v) := by
    simpa [A] using realCl06ToRealMatrix8BlockLin_sq v
  have hanti : A * W + W * A = 0 := by
    simpa [A, W] using realCl06ToRealMatrix8BlockLin_mul_volume_add_volume_mul v
  have hW : W * W = -1 := by
    simp [W]
  calc
    (A + r • W) * (A + r • W) =
        A * A + r • (A * W + W * A) + (r * r) • (W * W) := by
      ext i j u w <;> fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases w <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four] <;>
        ring
    _ = algebraMap ℝ RealMatrix8Block (realCl06Form v - r * r) := by
      rw [hanti, smul_zero, add_zero, hsq, hW]
      simp [sub_eq_add_neg, Algebra.smul_def]

/-- The product target used for the full `Cl(0,7)` row. -/
abbrev RealMatrix8BlockProd := RealMatrix8Block × RealMatrix8Block

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 20000000 in
/-- The seven-generator real block-matrix product model for `Cl(0,7)`. -/
def realCl07ToRealMatrix8BlockProdLin :
    ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) →ₗ[ℝ] RealMatrix8BlockProd where
  toFun v :=
    (realCl06ToRealMatrix8BlockLin v.1 + v.2 • realCl06VolumeBlock,
      realCl06ToRealMatrix8BlockLin v.1 - v.2 • realCl06VolumeBlock)
  map_add' x y := by
    obtain ⟨x, r⟩ := x
    obtain ⟨y, s⟩ := y
    ext i j u v <;> fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases v <;>
      simp [realCl06ToRealMatrix8BlockLin, complexLinearRealBlock4, complexMatrix4Re,
        complexMatrix4Im, realCl06SixthBlock, realCl06ConjMatrixP,
        realCl05ToComplexMatrix4Mat, realCl06VolumeBlock] <;>
      ring
  map_smul' a x := by
    obtain ⟨x, r⟩ := x
    ext i j u v <;> fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases v <;>
      simp [realCl06ToRealMatrix8BlockLin, complexLinearRealBlock4, complexMatrix4Re,
        complexMatrix4Im, realCl06SixthBlock, realCl06ConjMatrixP,
        realCl05ToComplexMatrix4Mat, realCl06VolumeBlock]

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 30000000 in
theorem realCl07ToRealMatrix8BlockProdLin_sq
    (v : ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl07ToRealMatrix8BlockProdLin v * realCl07ToRealMatrix8BlockProdLin v =
      algebraMap ℝ RealMatrix8BlockProd (realCl07Form v) := by
  obtain ⟨x, r⟩ := v
  apply Prod.ext
  · simpa [realCl07ToRealMatrix8BlockProdLin, realCl07Form, realCl06Form,
      realCl05Form] using
      realCl06ToRealMatrix8BlockLin_add_smul_volume_sq x r
  · simpa [realCl07ToRealMatrix8BlockProdLin, sub_eq_add_neg, realCl07Form,
      realCl06Form, realCl05Form] using
      realCl06ToRealMatrix8BlockLin_add_smul_volume_sq x (-r)

/-- The explicit product representation of `Cl(0,7)`. -/
noncomputable def realCl07ToRealMatrix8BlockProd :
    CliffordAlgebra realCl07Form →ₐ[ℝ] RealMatrix8BlockProd :=
  CliffordAlgebra.lift realCl07Form ⟨realCl07ToRealMatrix8BlockProdLin,
    realCl07ToRealMatrix8BlockProdLin_sq⟩

@[simp]
theorem realCl07ToRealMatrix8BlockProd_ι
    (v : ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl07ToRealMatrix8BlockProd (CliffordAlgebra.ι realCl07Form v) =
      realCl07ToRealMatrix8BlockProdLin v := by
  simpa [realCl07ToRealMatrix8BlockProd] using
    (CliffordAlgebra.lift_ι_apply realCl07ToRealMatrix8BlockProdLin
      realCl07ToRealMatrix8BlockProdLin_sq v)

/-- Include the first six negative generators of `Cl(0,7)` as a copy of `Cl(0,6)`. -/
noncomputable def realCl06IntoCl07Lin :
    (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) →ₗ[ℝ] CliffordAlgebra realCl07Form where
  toFun v := CliffordAlgebra.ι realCl07Form (v, 0)
  map_add' x y := by
    simpa using
      (map_add (CliffordAlgebra.ι realCl07Form) (x, (0 : ℝ)) (y, (0 : ℝ)))
  map_smul' a x := by
    simpa using
      (map_smul (CliffordAlgebra.ι realCl07Form) a (x, (0 : ℝ)))

theorem realCl06IntoCl07Lin_sq (v : (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl06IntoCl07Lin v * realCl06IntoCl07Lin v =
      algebraMap ℝ (CliffordAlgebra realCl07Form) (realCl06Form v) := by
  rw [realCl06IntoCl07Lin, LinearMap.coe_mk, AddHom.coe_mk,
    CliffordAlgebra.ι_sq_scalar]
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := v
  simp [realCl07Form, realCl06Form, realCl05Form]

/-- The canonical copy of `Cl(0,6)` inside `Cl(0,7)`. -/
noncomputable def realCl06IntoCl07 :
    CliffordAlgebra realCl06Form →ₐ[ℝ] CliffordAlgebra realCl07Form :=
  CliffordAlgebra.lift realCl06Form ⟨realCl06IntoCl07Lin, realCl06IntoCl07Lin_sq⟩

@[simp]
theorem realCl06IntoCl07_ι (v : (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl06IntoCl07 (CliffordAlgebra.ι realCl06Form v) =
      CliffordAlgebra.ι realCl07Form (v, 0) := by
  simpa [realCl06IntoCl07, realCl06IntoCl07Lin] using
    (CliffordAlgebra.lift_ι_apply realCl06IntoCl07Lin realCl06IntoCl07Lin_sq v)

theorem realCl07ToRealMatrix8BlockProd_realCl06IntoCl07
    (x : CliffordAlgebra realCl06Form) :
    realCl07ToRealMatrix8BlockProd (realCl06IntoCl07 x) =
      (realCl06ToRealMatrix8Block x, realCl06ToRealMatrix8Block x) := by
  let F : CliffordAlgebra realCl06Form →ₐ[ℝ] RealMatrix8BlockProd :=
    realCl07ToRealMatrix8BlockProd.comp realCl06IntoCl07
  let G : CliffordAlgebra realCl06Form →ₐ[ℝ] RealMatrix8BlockProd :=
    realCl06ToRealMatrix8Block.prod realCl06ToRealMatrix8Block
  have hFG : F = G := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    ext i j u w <;> fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases w <;>
      simp [F, G, realCl07ToRealMatrix8BlockProd_ι, realCl06ToRealMatrix8Block_ι,
        realCl07ToRealMatrix8BlockProdLin]
  change F x = G x
  rw [hFG]

/-- The seventh negative generator of `Cl(0,7)`. -/
noncomputable def realCl07SeventhGenerator : CliffordAlgebra realCl07Form :=
  CliffordAlgebra.ι realCl07Form
    ((0 : (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)), (1 : ℝ))

@[simp]
theorem realCl07ToRealMatrix8BlockProd_seventhGenerator :
    realCl07ToRealMatrix8BlockProd realCl07SeventhGenerator =
      (realCl06VolumeBlock, -realCl06VolumeBlock) := by
  simp [realCl07SeventhGenerator, realCl07ToRealMatrix8BlockProdLin]

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 10000000 in
theorem realCl07ToRealMatrix8BlockProd_surjective :
    Function.Surjective realCl07ToRealMatrix8BlockProd := by
  intro A
  let X : RealMatrix8Block := (2⁻¹ : ℝ) • (A.1 + A.2)
  let D : RealMatrix8Block := (2⁻¹ : ℝ) • (A.1 - A.2)
  let Y : RealMatrix8Block := -realCl06VolumeBlock * D
  rcases realCl06ToRealMatrix8Block_surjective X with ⟨x, hx⟩
  rcases realCl06ToRealMatrix8Block_surjective Y with ⟨y, hy⟩
  refine ⟨realCl06IntoCl07 x + realCl07SeventhGenerator * realCl06IntoCl07 y, ?_⟩
  rw [map_add, map_mul, realCl07ToRealMatrix8BlockProd_realCl06IntoCl07 x,
    realCl07ToRealMatrix8BlockProd_realCl06IntoCl07 y,
    realCl07ToRealMatrix8BlockProd_seventhGenerator, hx, hy]
  have hWY : realCl06VolumeBlock * Y = D := by
    dsimp [Y]
    rw [← mul_assoc, mul_neg, realCl06VolumeBlock_sq]
    simpa only [neg_mul, neg_one_mul, one_mul] using (neg_neg D)
  have hnegWY : -realCl06VolumeBlock * Y = -D := by
    rw [neg_mul, hWY]
  ext i j u v <;> fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases v <;>
    simp [X, D, hWY, hnegWY] <;>
    ring_nf

theorem realCl07Clifford_finrank :
    Module.finrank ℝ (CliffordAlgebra realCl07Form) = 128 := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hfin :
      Module.finrank ℝ ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) = 7 := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
      Module.finrank_prod, Module.finrank_prod, Module.finrank_prod]
    norm_num
  calc
    Module.finrank ℝ (CliffordAlgebra realCl07Form) =
        Module.finrank ℝ (ExteriorAlgebra ℝ
          ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) := by
      exact LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior realCl07Form)
    _ = 2 ^ Module.finrank ℝ ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) := by
      exact ExteriorAlgebra.finrank_eq_two_pow (K := ℝ)
    _ = 128 := by
      rw [hfin]
      norm_num

theorem realCl07RealMatrix8BlockProd_finrank :
    Module.finrank ℝ RealMatrix8BlockProd = 128 := by
  rw [Module.finrank_prod]
  norm_num [realCl06RealMatrix8Block_finrank]

theorem realCl07ToRealMatrix8BlockProd_injective :
    Function.Injective realCl07ToRealMatrix8BlockProd := by
  have hcl_succ : Module.finrank ℝ (CliffordAlgebra realCl07Form) = Nat.succ 127 := by
    simpa using realCl07Clifford_finrank
  letI : FiniteDimensional ℝ (CliffordAlgebra realCl07Form) :=
    FiniteDimensional.of_finrank_eq_succ hcl_succ
  have hdim : Module.finrank ℝ (CliffordAlgebra realCl07Form) =
      Module.finrank ℝ RealMatrix8BlockProd := by
    rw [realCl07Clifford_finrank, realCl07RealMatrix8BlockProd_finrank]
  simpa using
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := realCl07ToRealMatrix8BlockProd.toLinearMap) hdim).mpr
      realCl07ToRealMatrix8BlockProd_surjective)

/-- The real Clifford algebra `Cl(0,7)` is a product of two `8 × 8` real block
matrix algebras. -/
noncomputable def realCl07EquivRealMatrix8BlockProd :
    CliffordAlgebra realCl07Form ≃ₐ[ℝ] RealMatrix8BlockProd :=
  AlgEquiv.ofBijective realCl07ToRealMatrix8BlockProd
    ⟨realCl07ToRealMatrix8BlockProd_injective,
      realCl07ToRealMatrix8BlockProd_surjective⟩

@[simp]
theorem realCl07EquivRealMatrix8BlockProd_apply_ι
    (v : ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl07EquivRealMatrix8BlockProd (CliffordAlgebra.ι realCl07Form v) =
      realCl07ToRealMatrix8BlockProdLin v := by
  simp [realCl07EquivRealMatrix8BlockProd]

/-- The canonical equivalence from the `2 × 2` block presentation of `Mat₈(ℝ)`
to the ordinary `8 × 8` matrix algebra. -/
noncomputable def realMatrix8BlockEquivMatrix8 :
    RealMatrix8Block ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  (Matrix.compAlgEquiv (Fin 2) (Fin 4) ℝ ℝ).trans
    (Matrix.reindexAlgEquiv ℝ ℝ (finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin (2 * 4)))

/-- The real Clifford algebra `Cl(0,7)` is the product
`Mat₈(ℝ) × Mat₈(ℝ)`. -/
noncomputable def realCl07EquivRealMatrix8Prod :
    CliffordAlgebra realCl07Form ≃ₐ[ℝ]
      Matrix (Fin 8) (Fin 8) ℝ × Matrix (Fin 8) (Fin 8) ℝ :=
  realCl07EquivRealMatrix8BlockProd.trans
    (AlgEquiv.prodCongr realMatrix8BlockEquivMatrix8 realMatrix8BlockEquivMatrix8)

namespace RealClassification

/-- Canonical quadratic form for `Cl(0,7)` and its even algebra in the
real-classification namespace. -/
noncomputable abbrev Q_0_7 :
    QuadraticForm ℝ ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) :=
  realCl07Form

/-- Canonical even real-classification entry: `Cl⁺(0,7) ≃ Mat₈(ℝ)`. -/
noncomputable def cl_0_7_even_equivMatrix8 :
    CliffordAlgebra.even Q_0_7 ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ := by
  simpa [Q_0_7] using realEvenCl07EquivRealMatrix8

/-- Canonical real-classification entry: `Cl(0,7) ≃ Mat₈(ℝ) × Mat₈(ℝ)`. -/
noncomputable def cl_0_7_equivMatrix8Prod :
    CliffordAlgebra Q_0_7 ≃ₐ[ℝ]
      Matrix (Fin 8) (Fin 8) ℝ × Matrix (Fin 8) (Fin 8) ℝ := by
  simpa [Q_0_7] using realCl07EquivRealMatrix8Prod

end RealClassification

end

end Spinor
