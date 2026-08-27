import Spinor.Cl07RealMatrixProd

/-!
  The negative eight-dimensional real Bott row.

  This file extends the proof-bearing negative real table with
  `Cl(0,8) ≃ Mat₁₆(ℝ)`.  The construction uses the product model for
  `Cl(0,7)`: the first seven generators act diagonally, and the eighth
  generator is the off-diagonal operator built from the `Cl(0,6)` volume block.
-/

namespace Spinor

noncomputable section

/-- The standard negative real 8-dimensional quadratic form on
`(((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)`. -/
noncomputable abbrev realCl08Form :
    QuadraticForm ℝ (((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) :=
  CliffordAlgebra.EquivEven.Q' realCl07Form

@[simp] theorem realCl08Form_apply (a b c d e f g h : ℝ) :
    realCl08Form (((((((a, b), c), d), e), f), g), h) =
      -(a * a + b * b + c * c + d * d + e * e + f * f + g * g + h * h) := by
  simp [realCl08Form, realCl07Form, realCl06Form, realCl05Form]
  ring

/-- The even real Clifford algebra `Cl⁺(0,8)` is isomorphic to
`Mat₈(ℝ) × Mat₈(ℝ)`. -/
noncomputable def realEvenCl08EquivRealMatrix8Prod :
    CliffordAlgebra.even realCl08Form ≃ₐ[ℝ]
      Matrix (Fin 8) (Fin 8) ℝ × Matrix (Fin 8) (Fin 8) ℝ := by
  simpa [realCl08Form] using
    ((CliffordAlgebra.equivEven realCl07Form).symm.trans realCl07EquivRealMatrix8Prod)

/-- The `2 × 2` block target over the `Cl(0,6)` real matrix block algebra used
for the full `Cl(0,8)` row. -/
abbrev RealMatrix16Block := Matrix (Fin 2) (Fin 2) RealMatrix8Block

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 5000000 in
theorem realCl07ToRealMatrix8BlockProdLin_fst_mul_volume_add_volume_mul_snd
    (v : ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    (realCl07ToRealMatrix8BlockProdLin v).1 * realCl06VolumeBlock +
        realCl06VolumeBlock * (realCl07ToRealMatrix8BlockProdLin v).2 = 0 := by
  obtain ⟨x, r⟩ := v
  let A := realCl06ToRealMatrix8BlockLin x
  let W := realCl06VolumeBlock
  have hanti : A * W + W * A = 0 := by
    simpa [A, W] using realCl06ToRealMatrix8BlockLin_mul_volume_add_volume_mul x
  calc
    (A + r • W) * W + W * (A - r • W) = A * W + W * A := by
      ext i j u w <;> fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases w <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four] <;>
        ring
    _ = 0 := hanti

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 5000000 in
theorem realCl07ToRealMatrix8BlockProdLin_volume_mul_fst_add_snd_mul_volume
    (v : ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl06VolumeBlock * (realCl07ToRealMatrix8BlockProdLin v).1 +
        (realCl07ToRealMatrix8BlockProdLin v).2 * realCl06VolumeBlock = 0 := by
  obtain ⟨x, r⟩ := v
  let A := realCl06ToRealMatrix8BlockLin x
  let W := realCl06VolumeBlock
  have hanti : W * A + A * W = 0 := by
    rw [add_comm]
    simpa [A, W] using realCl06ToRealMatrix8BlockLin_mul_volume_add_volume_mul x
  calc
    W * (A + r • W) + (A - r • W) * W = W * A + A * W := by
      ext i j u w <;> fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases w <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four] <;>
        ring
    _ = 0 := hanti

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 5000000 in
theorem realCl06VolumeBlock_smul_mul_smul (r : ℝ) :
    (r • realCl06VolumeBlock) * (r • realCl06VolumeBlock) =
      algebraMap ℝ RealMatrix8Block (-(r * r)) := by
  rw [smul_mul_assoc, mul_smul_comm, realCl06VolumeBlock_sq]
  simp [Algebra.smul_def]

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 12000000 in
/-- The eight-generator real block-matrix model for `Cl(0,8)`. -/
def realCl08ToRealMatrix16BlockLin :
    (((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) →ₗ[ℝ] RealMatrix16Block where
  toFun v :=
    let p := realCl07ToRealMatrix8BlockProdLin v.1
    !![p.1, v.2 • realCl06VolumeBlock;
       v.2 • realCl06VolumeBlock, p.2]
  map_add' x y := by
    obtain ⟨x, r⟩ := x
    obtain ⟨y, s⟩ := y
    ext i j u v a b <;> fin_cases i <;> fin_cases j <;> fin_cases u <;>
      fin_cases v <;> fin_cases a <;> fin_cases b <;>
      simp [realCl07ToRealMatrix8BlockProdLin, realCl06ToRealMatrix8BlockLin,
        complexLinearRealBlock4, complexMatrix4Re, complexMatrix4Im, realCl06SixthBlock,
        realCl06ConjMatrixP, realCl05ToComplexMatrix4Mat, realCl06VolumeBlock] <;>
      ring
  map_smul' a x := by
    obtain ⟨x, r⟩ := x
    ext i j u v b c <;> fin_cases i <;> fin_cases j <;> fin_cases u <;>
      fin_cases v <;> fin_cases b <;> fin_cases c <;>
      simp [realCl07ToRealMatrix8BlockProdLin, realCl06ToRealMatrix8BlockLin,
        complexLinearRealBlock4, complexMatrix4Re, complexMatrix4Im, realCl06SixthBlock,
        realCl06ConjMatrixP, realCl05ToComplexMatrix4Mat, realCl06VolumeBlock]

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 12000000 in
theorem realCl08ToRealMatrix16BlockLin_sq
    (v : (((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl08ToRealMatrix16BlockLin v * realCl08ToRealMatrix16BlockLin v =
      algebraMap ℝ RealMatrix16Block (realCl08Form v) := by
  obtain ⟨x, r⟩ := v
  let p := realCl07ToRealMatrix8BlockProdLin x
  have hp := realCl07ToRealMatrix8BlockProdLin_sq x
  have hp1 : p.1 * p.1 = algebraMap ℝ RealMatrix8Block (realCl07Form x) := by
    simpa [p] using congrArg Prod.fst hp
  have hp2 : p.2 * p.2 = algebraMap ℝ RealMatrix8Block (realCl07Form x) := by
    simpa [p] using congrArg Prod.snd hp
  have hW : (r • realCl06VolumeBlock) * (r • realCl06VolumeBlock) =
      algebraMap ℝ RealMatrix8Block (-(r * r)) :=
    realCl06VolumeBlock_smul_mul_smul r
  have h01 :
      p.1 * (r • realCl06VolumeBlock) + (r • realCl06VolumeBlock) * p.2 = 0 := by
    have h := realCl07ToRealMatrix8BlockProdLin_fst_mul_volume_add_volume_mul_snd x
    calc
      p.1 * (r • realCl06VolumeBlock) + (r • realCl06VolumeBlock) * p.2 =
          r • (p.1 * realCl06VolumeBlock + realCl06VolumeBlock * p.2) := by
        rw [mul_smul_comm, smul_mul_assoc, smul_add]
      _ = 0 := by
        simp [p, h]
  have h10 :
      (r • realCl06VolumeBlock) * p.1 + p.2 * (r • realCl06VolumeBlock) = 0 := by
    have h := realCl07ToRealMatrix8BlockProdLin_volume_mul_fst_add_snd_mul_volume x
    calc
      (r • realCl06VolumeBlock) * p.1 + p.2 * (r • realCl06VolumeBlock) =
          r • (realCl06VolumeBlock * p.1 + p.2 * realCl06VolumeBlock) := by
        rw [smul_mul_assoc, mul_smul_comm, smul_add]
      _ = 0 := by
        simp [p, h]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change
      p.1 * p.1 + (r • realCl06VolumeBlock) * (r • realCl06VolumeBlock) =
        algebraMap ℝ RealMatrix8Block (realCl08Form (x, r))
    rw [hp1, hW, ← map_add]
    congr 1
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change p.1 * (r • realCl06VolumeBlock) + (r • realCl06VolumeBlock) * p.2 = 0
    exact h01
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change (r • realCl06VolumeBlock) * p.1 + p.2 * (r • realCl06VolumeBlock) = 0
    exact h10
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change
      (r • realCl06VolumeBlock) * (r • realCl06VolumeBlock) + p.2 * p.2 =
        algebraMap ℝ RealMatrix8Block (realCl08Form (x, r))
    rw [hp2, hW, add_comm, ← map_add]
    congr 1

/-- The explicit real block-matrix representation of `Cl(0,8)`. -/
noncomputable def realCl08ToRealMatrix16Block :
    CliffordAlgebra realCl08Form →ₐ[ℝ] RealMatrix16Block :=
  CliffordAlgebra.lift realCl08Form ⟨realCl08ToRealMatrix16BlockLin,
    realCl08ToRealMatrix16BlockLin_sq⟩

@[simp]
theorem realCl08ToRealMatrix16Block_ι
    (v : (((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl08ToRealMatrix16Block (CliffordAlgebra.ι realCl08Form v) =
      realCl08ToRealMatrix16BlockLin v := by
  simpa [realCl08ToRealMatrix16Block] using
    (CliffordAlgebra.lift_ι_apply realCl08ToRealMatrix16BlockLin
      realCl08ToRealMatrix16BlockLin_sq v)

/-- Include the first seven negative generators of `Cl(0,8)` as a copy of `Cl(0,7)`. -/
noncomputable def realCl07IntoCl08Lin :
    ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) →ₗ[ℝ] CliffordAlgebra realCl08Form where
  toFun v := CliffordAlgebra.ι realCl08Form (v, 0)
  map_add' x y := by
    simpa using
      (map_add (CliffordAlgebra.ι realCl08Form) (x, (0 : ℝ)) (y, (0 : ℝ)))
  map_smul' a x := by
    simpa using
      (map_smul (CliffordAlgebra.ι realCl08Form) a (x, (0 : ℝ)))

theorem realCl07IntoCl08Lin_sq (v : ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl07IntoCl08Lin v * realCl07IntoCl08Lin v =
      algebraMap ℝ (CliffordAlgebra realCl08Form) (realCl07Form v) := by
  rw [realCl07IntoCl08Lin, LinearMap.coe_mk, AddHom.coe_mk,
    CliffordAlgebra.ι_sq_scalar]
  obtain ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩ := v
  simp [realCl08Form, realCl07Form, realCl06Form, realCl05Form]

/-- The canonical copy of `Cl(0,7)` inside `Cl(0,8)`. -/
noncomputable def realCl07IntoCl08 :
    CliffordAlgebra realCl07Form →ₐ[ℝ] CliffordAlgebra realCl08Form :=
  CliffordAlgebra.lift realCl07Form ⟨realCl07IntoCl08Lin, realCl07IntoCl08Lin_sq⟩

set_option maxHeartbeats 2000000 in
@[simp]
theorem realCl07IntoCl08_ι (v : ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl07IntoCl08 (CliffordAlgebra.ι realCl07Form v) =
      CliffordAlgebra.ι realCl08Form (v, 0) := by
  simpa [realCl07IntoCl08, realCl07IntoCl08Lin] using
    (CliffordAlgebra.lift_ι_apply realCl07IntoCl08Lin realCl07IntoCl08Lin_sq v)

theorem realCl08ToRealMatrix16Block_realCl07IntoCl08
    (x : CliffordAlgebra realCl07Form) :
    realCl08ToRealMatrix16Block (realCl07IntoCl08 x) =
      let p := realCl07ToRealMatrix8BlockProd x
      !![p.1, 0; 0, p.2] := by
  let F : CliffordAlgebra realCl07Form →ₐ[ℝ] RealMatrix16Block :=
    realCl08ToRealMatrix16Block.comp realCl07IntoCl08
  let G : CliffordAlgebra realCl07Form →ₐ[ℝ] RealMatrix16Block := {
    toFun := fun x =>
      let p := realCl07ToRealMatrix8BlockProd x
      !![p.1, 0; 0, p.2]
    map_zero' := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp
    map_one' := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp
    map_add' x y := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp
    map_mul' x y := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    commutes' r := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.algebraMap_matrix_apply]
  }
  have hFG : F = G := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [F, G, realCl08ToRealMatrix16Block_ι, realCl07ToRealMatrix8BlockProd_ι,
        realCl08ToRealMatrix16BlockLin]
  change F x = G x
  rw [hFG]

/-- The eighth negative generator of `Cl(0,8)`. -/
noncomputable def realCl08EighthGenerator : CliffordAlgebra realCl08Form :=
  CliffordAlgebra.ι realCl08Form
    ((0 : ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)), (1 : ℝ))

@[simp]
theorem realCl08ToRealMatrix16Block_eighthGenerator :
    realCl08ToRealMatrix16Block realCl08EighthGenerator =
      !![0, realCl06VolumeBlock; realCl06VolumeBlock, 0] := by
  simp [realCl08EighthGenerator, realCl08ToRealMatrix16BlockLin]

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 12000000 in
theorem realCl08ToRealMatrix16Block_surjective :
    Function.Surjective realCl08ToRealMatrix16Block := by
  intro A
  rcases realCl07ToRealMatrix8BlockProd_surjective (A 0 0, A 1 1) with ⟨x, hx⟩
  let Y : RealMatrix8BlockProd :=
    (-realCl06VolumeBlock * A 1 0, -realCl06VolumeBlock * A 0 1)
  rcases realCl07ToRealMatrix8BlockProd_surjective Y with ⟨y, hy⟩
  refine ⟨realCl07IntoCl08 x + realCl08EighthGenerator * realCl07IntoCl08 y, ?_⟩
  rw [map_add, map_mul, realCl08ToRealMatrix16Block_realCl07IntoCl08 x,
    realCl08ToRealMatrix16Block_realCl07IntoCl08 y,
    realCl08ToRealMatrix16Block_eighthGenerator, hx, hy]
  have h10 : realCl06VolumeBlock * (-realCl06VolumeBlock * A 1 0) = A 1 0 := by
    rw [← mul_assoc, mul_neg, realCl06VolumeBlock_sq]
    simpa only [neg_mul, neg_one_mul, one_mul] using (neg_neg (A 1 0))
  have h01 : realCl06VolumeBlock * (-realCl06VolumeBlock * A 0 1) = A 0 1 := by
    rw [← mul_assoc, mul_neg, realCl06VolumeBlock_sq]
    simpa only [neg_mul, neg_one_mul, one_mul] using (neg_neg (A 0 1))
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simp [Y]
  · simpa [Y] using h01
  · simpa [Y] using h10
  · simp [Y]

theorem realCl08Clifford_finrank :
    Module.finrank ℝ (CliffordAlgebra realCl08Form) = 256 := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hfin :
      Module.finrank ℝ (((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) = 8 := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
      Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
      Module.finrank_prod]
    norm_num
  calc
    Module.finrank ℝ (CliffordAlgebra realCl08Form) =
        Module.finrank ℝ (ExteriorAlgebra ℝ
          (((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) := by
      exact LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior realCl08Form)
    _ = 2 ^ Module.finrank ℝ (((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) := by
      exact ExteriorAlgebra.finrank_eq_two_pow (K := ℝ)
    _ = 256 := by
      rw [hfin]
      norm_num

theorem realCl08RealMatrix16Block_finrank :
    Module.finrank ℝ RealMatrix16Block = 256 := by
  rw [Module.finrank_matrix]
  norm_num [realCl06RealMatrix8Block_finrank]

theorem realCl08ToRealMatrix16Block_injective :
    Function.Injective realCl08ToRealMatrix16Block := by
  have hcl_succ : Module.finrank ℝ (CliffordAlgebra realCl08Form) = Nat.succ 255 := by
    simpa using realCl08Clifford_finrank
  letI : FiniteDimensional ℝ (CliffordAlgebra realCl08Form) :=
    FiniteDimensional.of_finrank_eq_succ hcl_succ
  have hdim : Module.finrank ℝ (CliffordAlgebra realCl08Form) =
      Module.finrank ℝ RealMatrix16Block := by
    rw [realCl08Clifford_finrank, realCl08RealMatrix16Block_finrank]
  simpa using
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := realCl08ToRealMatrix16Block.toLinearMap) hdim).mpr
      realCl08ToRealMatrix16Block_surjective)

/-- The real Clifford algebra `Cl(0,8)` is a `2 × 2` block matrix algebra over
the explicit `Cl(0,6)` real matrix block target. -/
noncomputable def realCl08EquivRealMatrix16Block :
    CliffordAlgebra realCl08Form ≃ₐ[ℝ] RealMatrix16Block :=
  AlgEquiv.ofBijective realCl08ToRealMatrix16Block
    ⟨realCl08ToRealMatrix16Block_injective,
      realCl08ToRealMatrix16Block_surjective⟩

@[simp]
theorem realCl08EquivRealMatrix16Block_apply_ι
    (v : (((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)) :
    realCl08EquivRealMatrix16Block (CliffordAlgebra.ι realCl08Form v) =
      realCl08ToRealMatrix16BlockLin v := by
  simp [realCl08EquivRealMatrix16Block]

/-- The real Clifford algebra `Cl(0,8)` is the full `16 × 16` real matrix algebra. -/
noncomputable def realCl08EquivRealMatrix16 :
    CliffordAlgebra realCl08Form ≃ₐ[ℝ] Matrix (Fin 16) (Fin 16) ℝ :=
  realCl08EquivRealMatrix16Block.trans
    ((realMatrix8BlockEquivMatrix8.mapMatrix).trans
      ((Matrix.compAlgEquiv (Fin 2) (Fin 8) ℝ ℝ).trans
        (Matrix.reindexAlgEquiv ℝ ℝ (finProdFinEquiv : Fin 2 × Fin 8 ≃ Fin (2 * 8)))))

namespace RealClassification

/-- Canonical quadratic form for `Cl(0,8)` and its even algebra in the
real-classification namespace. -/
noncomputable abbrev Q_0_8 :
    QuadraticForm ℝ (((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) :=
  realCl08Form

/-- Canonical even real-classification entry:
`Cl⁺(0,8) ≃ Mat₈(ℝ) × Mat₈(ℝ)`. -/
noncomputable def cl_0_8_even_equivMatrix8Prod :
    CliffordAlgebra.even Q_0_8 ≃ₐ[ℝ]
      Matrix (Fin 8) (Fin 8) ℝ × Matrix (Fin 8) (Fin 8) ℝ := by
  simpa [Q_0_8] using realEvenCl08EquivRealMatrix8Prod

/-- Canonical real-classification entry: `Cl(0,8) ≃ Mat₁₆(ℝ)`. -/
noncomputable def cl_0_8_equivMatrix16 :
    CliffordAlgebra Q_0_8 ≃ₐ[ℝ] Matrix (Fin 16) (Fin 16) ℝ := by
  simpa [Q_0_8] using realCl08EquivRealMatrix16

end RealClassification

end

end Spinor
