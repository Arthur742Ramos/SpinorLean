import Spinor.Cl08RealMatrix

/-!
  Positive seven- and eight-dimensional real Bott rows.

  This file records the positive-signature `Cl(7,0)` row, together with
  positive-signature even rows obtained from the corresponding negative rows by
  Mathlib's even-Clifford sign-change equivalence.
-/

namespace Spinor

noncomputable section

abbrev RealCl06Space := (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)

abbrev RealCl07Space := ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)

abbrev RealCl08Space := RealCl07Space × ℝ

/-- The standard positive real 7-dimensional quadratic form on
`((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)`. -/
noncomputable abbrev realCl70Form : QuadraticForm ℝ RealCl07Space :=
  -realCl07Form

@[simp] theorem realCl70Form_apply (a b c d e f g : ℝ) :
    realCl70Form ((((((a, b), c), d), e), f), g) =
      a * a + b * b + c * c + d * d + e * e + f * f + g * g := by
  simp [realCl70Form, realCl07Form, realCl06Form, realCl05Form]
  ring

/-- The even real Clifford algebra `Cl⁺(7,0)` is isomorphic to `Mat₈(ℝ)`. -/
noncomputable def realEvenCl70EquivRealMatrix8 :
    CliffordAlgebra.even realCl70Form ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ := by
  simpa [realCl70Form] using
    ((CliffordAlgebra.evenEquivEvenNeg (Q := realCl07Form)).symm.trans
      realEvenCl07EquivRealMatrix8)

def realCl06BasisVector1 : RealCl06Space := (((((1, 0), 0), 0), 0), 0)

def realCl06BasisVector2 : RealCl06Space := (((((0, 1), 0), 0), 0), 0)

def realCl06BasisVector3 : RealCl06Space := (((((0, 0), 1), 0), 0), 0)

def realCl06BasisVector4 : RealCl06Space := (((((0, 0), 0), 1), 0), 0)

def realCl06BasisVector5 : RealCl06Space := (((((0, 0), 0), 0), 1), 0)

def realCl06BasisVector6 : RealCl06Space := (((((0, 0), 0), 0), 0), 1)

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 30000000 in
theorem realCl06VolumeBlock_eq_generator_product :
    realCl06ToRealMatrix8BlockLin realCl06BasisVector1 *
      realCl06ToRealMatrix8BlockLin realCl06BasisVector2 *
      realCl06ToRealMatrix8BlockLin realCl06BasisVector3 *
      realCl06ToRealMatrix8BlockLin realCl06BasisVector4 *
      realCl06ToRealMatrix8BlockLin realCl06BasisVector5 *
      realCl06ToRealMatrix8BlockLin realCl06BasisVector6 = realCl06VolumeBlock := by
  ext i j u v <;> fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases v <;>
    simp [realCl06BasisVector1, realCl06BasisVector2, realCl06BasisVector3,
      realCl06BasisVector4, realCl06BasisVector5, realCl06BasisVector6,
      realCl06ToRealMatrix8BlockLin, complexLinearRealBlock4, complexMatrix4Re,
      complexMatrix4Im, realCl06SixthBlock, realCl06ConjMatrixP,
      realCl05ToComplexMatrix4Mat, realCl06VolumeBlock,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

def realCl07BasisVector1 : RealCl07Space := (realCl06BasisVector1, 0)

def realCl07BasisVector2 : RealCl07Space := (realCl06BasisVector2, 0)

def realCl07BasisVector3 : RealCl07Space := (realCl06BasisVector3, 0)

def realCl07BasisVector4 : RealCl07Space := (realCl06BasisVector4, 0)

def realCl07BasisVector5 : RealCl07Space := (realCl06BasisVector5, 0)

def realCl07BasisVector6 : RealCl07Space := (realCl06BasisVector6, 0)

def realCl07BasisVector7 : RealCl07Space := (0, 1)

theorem realCl07_firstComponent_basis_product :
    (realCl07ToRealMatrix8BlockProdLin realCl07BasisVector1).1 *
      (realCl07ToRealMatrix8BlockProdLin realCl07BasisVector2).1 *
      (realCl07ToRealMatrix8BlockProdLin realCl07BasisVector3).1 *
      (realCl07ToRealMatrix8BlockProdLin realCl07BasisVector4).1 *
      (realCl07ToRealMatrix8BlockProdLin realCl07BasisVector5).1 *
      (realCl07ToRealMatrix8BlockProdLin realCl07BasisVector6).1 *
      (realCl07ToRealMatrix8BlockProdLin realCl07BasisVector7).1 = -1 := by
  simp [realCl07BasisVector1, realCl07BasisVector2, realCl07BasisVector3,
    realCl07BasisVector4, realCl07BasisVector5, realCl07BasisVector6,
    realCl07BasisVector7, realCl07ToRealMatrix8BlockProdLin]
  rw [realCl06VolumeBlock_eq_generator_product]
  simp [realCl06VolumeBlock_sq]

noncomputable def realToComplexAlgHom : ℝ →ₐ[ℝ] ℂ where
  toRingHom := algebraMap ℝ ℂ
  commutes' := by intro r; rfl

noncomputable def realMatrix8BlockToComplexMatrix8 :
    RealMatrix8Block →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℂ :=
  (AlgHom.mapMatrix realToComplexAlgHom).comp
    realMatrix8BlockEquivMatrix8.toAlgHom

def complexMatrix8Re (A : Matrix (Fin 8) (Fin 8) ℂ) : Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j => (A i j).re

def complexMatrix8Im (A : Matrix (Fin 8) (Fin 8) ℂ) : Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j => (A i j).im

theorem complexMatrix8_decompose (A : Matrix (Fin 8) (Fin 8) ℂ) :
    A = realMatrix8BlockToComplexMatrix8
          (realMatrix8BlockEquivMatrix8.symm (complexMatrix8Re A)) +
        (Complex.I • (1 : Matrix (Fin 8) (Fin 8) ℂ)) *
          realMatrix8BlockToComplexMatrix8
            (realMatrix8BlockEquivMatrix8.symm (complexMatrix8Im A)) := by
  ext i j
  simp [realMatrix8BlockToComplexMatrix8, realToComplexAlgHom, complexMatrix8Re,
    complexMatrix8Im]
  rw [mul_comm]
  exact (Complex.re_add_im (A i j)).symm

/-- The seven-generator complex matrix model for `Cl(7,0)`. -/
def realCl70ToComplexMatrix8Lin :
    RealCl07Space →ₗ[ℝ] Matrix (Fin 8) (Fin 8) ℂ where
  toFun v := Complex.I • realMatrix8BlockToComplexMatrix8
    (realCl07ToRealMatrix8BlockProdLin v).1
  map_add' x y := by
    simp [map_add]
  map_smul' a x := by
    rw [map_smul, Prod.smul_fst]
    rw [map_smul]
    exact (smul_comm (a : ℝ) Complex.I
      (realMatrix8BlockToComplexMatrix8 (realCl07ToRealMatrix8BlockProdLin x).1)).symm

theorem realCl70ToComplexMatrix8Lin_sq (v : RealCl07Space) :
    realCl70ToComplexMatrix8Lin v * realCl70ToComplexMatrix8Lin v =
      algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℂ) (realCl70Form v) := by
  let A := realMatrix8BlockToComplexMatrix8 (realCl07ToRealMatrix8BlockProdLin v).1
  have hp := realCl07ToRealMatrix8BlockProdLin_sq v
  have hp1 :
      (realCl07ToRealMatrix8BlockProdLin v).1 *
          (realCl07ToRealMatrix8BlockProdLin v).1 =
        algebraMap ℝ RealMatrix8Block (realCl07Form v) := by
    simpa using congrArg Prod.fst hp
  calc
    realCl70ToComplexMatrix8Lin v * realCl70ToComplexMatrix8Lin v = -(A * A) := by
      simp [realCl70ToComplexMatrix8Lin, A, smul_smul, Complex.I_mul_I]
    _ = -realMatrix8BlockToComplexMatrix8
        ((realCl07ToRealMatrix8BlockProdLin v).1 *
          (realCl07ToRealMatrix8BlockProdLin v).1) := by
        rw [map_mul]
    _ = algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℂ) (realCl70Form v) := by
        rw [hp1]
        simp [realCl70Form]

/-- The explicit representation of `Cl(7,0)` in `8 × 8` complex matrices. -/
noncomputable def realCl70ToComplexMatrix8 :
    CliffordAlgebra realCl70Form →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℂ :=
  CliffordAlgebra.lift realCl70Form ⟨realCl70ToComplexMatrix8Lin,
    realCl70ToComplexMatrix8Lin_sq⟩

@[simp]
theorem realCl70ToComplexMatrix8_ι (v : RealCl07Space) :
    realCl70ToComplexMatrix8 (CliffordAlgebra.ι realCl70Form v) =
      realCl70ToComplexMatrix8Lin v := by
  simpa [realCl70ToComplexMatrix8] using
    (CliffordAlgebra.lift_ι_apply realCl70ToComplexMatrix8Lin
      realCl70ToComplexMatrix8Lin_sq v)

/-- The ordered product of the seven positive generators in the `Cl(7,0)` model. -/
noncomputable def realCl70VolumeElement : CliffordAlgebra realCl70Form :=
  CliffordAlgebra.ι realCl70Form realCl07BasisVector1 *
    CliffordAlgebra.ι realCl70Form realCl07BasisVector2 *
    CliffordAlgebra.ι realCl70Form realCl07BasisVector3 *
    CliffordAlgebra.ι realCl70Form realCl07BasisVector4 *
    CliffordAlgebra.ι realCl70Form realCl07BasisVector5 *
    CliffordAlgebra.ι realCl70Form realCl07BasisVector6 *
    CliffordAlgebra.ι realCl70Form realCl07BasisVector7

theorem realCl70ToComplexMatrix8_volumeElement :
    realCl70ToComplexMatrix8 realCl70VolumeElement =
      Complex.I • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  have hprod :
      realMatrix8BlockToComplexMatrix8 (realCl07ToRealMatrix8BlockProdLin
          realCl07BasisVector1).1 *
        realMatrix8BlockToComplexMatrix8 (realCl07ToRealMatrix8BlockProdLin
          realCl07BasisVector2).1 *
        realMatrix8BlockToComplexMatrix8 (realCl07ToRealMatrix8BlockProdLin
          realCl07BasisVector3).1 *
        realMatrix8BlockToComplexMatrix8 (realCl07ToRealMatrix8BlockProdLin
          realCl07BasisVector4).1 *
        realMatrix8BlockToComplexMatrix8 (realCl07ToRealMatrix8BlockProdLin
          realCl07BasisVector5).1 *
        realMatrix8BlockToComplexMatrix8 (realCl07ToRealMatrix8BlockProdLin
          realCl07BasisVector6).1 *
        realMatrix8BlockToComplexMatrix8 (realCl07ToRealMatrix8BlockProdLin
          realCl07BasisVector7).1 = -1 := by
    simpa [map_mul] using
      congrArg realMatrix8BlockToComplexMatrix8 realCl07_firstComponent_basis_product
  simp [realCl70VolumeElement, map_mul, realCl70ToComplexMatrix8Lin, hprod,
    smul_smul, Complex.I_mul_I]

theorem realCl70_realMatrix8BlockToComplexMatrix8_mem_range_of_I_mem
    (hI : (Complex.I • (1 : Matrix (Fin 8) (Fin 8) ℂ)) ∈ realCl70ToComplexMatrix8.range)
    (A : RealMatrix8Block) :
    realMatrix8BlockToComplexMatrix8 A ∈ realCl70ToComplexMatrix8.range := by
  let S : Subalgebra ℝ (Matrix (Fin 8) (Fin 8) ℂ) := realCl70ToComplexMatrix8.range
  have hnegI : (-(Complex.I • (1 : Matrix (Fin 8) (Fin 8) ℂ))) ∈ S := S.neg_mem hI
  have hgen : ∀ v : RealCl07Space,
      realMatrix8BlockToComplexMatrix8 (realCl07ToRealMatrix8BlockProdLin v).1 ∈ S := by
    intro v
    have hv : realCl70ToComplexMatrix8 (CliffordAlgebra.ι realCl70Form v) ∈ S :=
      ⟨CliffordAlgebra.ι realCl70Form v, rfl⟩
    have hmul :
        realMatrix8BlockToComplexMatrix8 (realCl07ToRealMatrix8BlockProdLin v).1 =
          (-(Complex.I • (1 : Matrix (Fin 8) (Fin 8) ℂ))) *
            realCl70ToComplexMatrix8 (CliffordAlgebra.ι realCl70Form v) := by
      simp [realCl70ToComplexMatrix8_ι, realCl70ToComplexMatrix8Lin,
        smul_smul, Complex.I_mul_I]
    rw [hmul]
    exact S.mul_mem hnegI hv
  have hx : ∀ x : CliffordAlgebra realCl07Form,
      realMatrix8BlockToComplexMatrix8 (realCl07ToRealMatrix8BlockProd x).1 ∈ S := by
    intro x
    induction x using CliffordAlgebra.induction with
    | algebraMap r =>
        simp [realCl07ToRealMatrix8BlockProd]
    | ι v =>
        simpa [realCl07ToRealMatrix8BlockProd_ι] using hgen v
    | add x y hx hy =>
        simpa [map_add] using S.add_mem hx hy
    | mul x y hx hy =>
        simpa [map_mul] using S.mul_mem hx hy
  rcases realCl07ToRealMatrix8BlockProd_surjective (A, 0) with ⟨x, hxA⟩
  have hxS := hx x
  have hfst : (realCl07ToRealMatrix8BlockProd x).1 = A := by
    simpa using congrArg Prod.fst hxA
  simpa [hfst] using hxS

theorem realCl70ToComplexMatrix8_surjective_of_I_mem
    (hI : (Complex.I • (1 : Matrix (Fin 8) (Fin 8) ℂ)) ∈ realCl70ToComplexMatrix8.range) :
    Function.Surjective realCl70ToComplexMatrix8 := by
  intro A
  let S : Subalgebra ℝ (Matrix (Fin 8) (Fin 8) ℂ) := realCl70ToComplexMatrix8.range
  have hre : realMatrix8BlockToComplexMatrix8
          (realMatrix8BlockEquivMatrix8.symm (complexMatrix8Re A)) ∈ S :=
    realCl70_realMatrix8BlockToComplexMatrix8_mem_range_of_I_mem hI _
  have him : realMatrix8BlockToComplexMatrix8
          (realMatrix8BlockEquivMatrix8.symm (complexMatrix8Im A)) ∈ S :=
    realCl70_realMatrix8BlockToComplexMatrix8_mem_range_of_I_mem hI _
  have hAim : (Complex.I • (1 : Matrix (Fin 8) (Fin 8) ℂ)) *
        realMatrix8BlockToComplexMatrix8
          (realMatrix8BlockEquivMatrix8.symm (complexMatrix8Im A)) ∈ S :=
    S.mul_mem hI him
  have hsum : A ∈ S := by
    rw [complexMatrix8_decompose A]
    exact S.add_mem hre hAim
  exact (AlgHom.mem_range realCl70ToComplexMatrix8).mp hsum

theorem realCl70ToComplexMatrix8_surjective :
    Function.Surjective realCl70ToComplexMatrix8 :=
  realCl70ToComplexMatrix8_surjective_of_I_mem
    ⟨realCl70VolumeElement, realCl70ToComplexMatrix8_volumeElement⟩

theorem realCl70Clifford_finrank :
    Module.finrank ℝ (CliffordAlgebra realCl70Form) = 128 := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hfin : Module.finrank ℝ RealCl07Space = 7 := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
      Module.finrank_prod, Module.finrank_prod, Module.finrank_prod]
    norm_num
  calc
    Module.finrank ℝ (CliffordAlgebra realCl70Form) =
        Module.finrank ℝ (ExteriorAlgebra ℝ RealCl07Space) := by
      exact LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior realCl70Form)
    _ = 2 ^ Module.finrank ℝ RealCl07Space := by
      exact ExteriorAlgebra.finrank_eq_two_pow (K := ℝ)
    _ = 128 := by
      rw [hfin]
      norm_num

theorem realCl70ComplexMatrix8_finrank :
    Module.finrank ℝ (Matrix (Fin 8) (Fin 8) ℂ) = 128 := by
  rw [Module.finrank_matrix]
  norm_num

theorem realCl70ToComplexMatrix8_injective :
    Function.Injective realCl70ToComplexMatrix8 := by
  have hcl_succ : Module.finrank ℝ (CliffordAlgebra realCl70Form) = Nat.succ 127 := by
    simpa using realCl70Clifford_finrank
  letI : FiniteDimensional ℝ (CliffordAlgebra realCl70Form) :=
    FiniteDimensional.of_finrank_eq_succ hcl_succ
  have hdim : Module.finrank ℝ (CliffordAlgebra realCl70Form) =
      Module.finrank ℝ (Matrix (Fin 8) (Fin 8) ℂ) := by
    rw [realCl70Clifford_finrank, realCl70ComplexMatrix8_finrank]
  simpa using
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := realCl70ToComplexMatrix8.toLinearMap) hdim).mpr
      realCl70ToComplexMatrix8_surjective)

/-- The real Clifford algebra `Cl(7,0)` is the full `8 × 8` complex matrix algebra. -/
noncomputable def realCl70EquivComplexMatrix8 :
    CliffordAlgebra realCl70Form ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℂ :=
  AlgEquiv.ofBijective realCl70ToComplexMatrix8
    ⟨realCl70ToComplexMatrix8_injective, realCl70ToComplexMatrix8_surjective⟩

/-- The standard positive real 8-dimensional quadratic form on
`(((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)`. -/
noncomputable abbrev realCl80Form : QuadraticForm ℝ RealCl08Space :=
  -realCl08Form

@[simp] theorem realCl80Form_apply (a b c d e f g h : ℝ) :
    realCl80Form (((((((a, b), c), d), e), f), g), h) =
      a * a + b * b + c * c + d * d + e * e + f * f + g * g + h * h := by
  simp [realCl80Form, realCl08Form, realCl07Form, realCl06Form, realCl05Form]
  ring

/-- The even real Clifford algebra `Cl⁺(8,0)` is isomorphic to
`Mat₈(ℝ) × Mat₈(ℝ)`. -/
noncomputable def realEvenCl80EquivRealMatrix8Prod :
    CliffordAlgebra.even realCl80Form ≃ₐ[ℝ]
      Matrix (Fin 8) (Fin 8) ℝ × Matrix (Fin 8) (Fin 8) ℝ := by
  simpa [realCl80Form] using
    ((CliffordAlgebra.evenEquivEvenNeg (Q := realCl08Form)).symm.trans
      realEvenCl08EquivRealMatrix8Prod)

/-- The real `16 × 16` block target coming from realifying complex `8 × 8`
matrices. -/
abbrev RealMatrix16ComplexBlock := Matrix (Fin 2) (Fin 2) (Matrix (Fin 8) (Fin 8) ℝ)

/-- The real block matrix of a complex-linear map on `ℂ⁸`. -/
def complexLinearRealBlock8 (A : Matrix (Fin 8) (Fin 8) ℂ) : RealMatrix16ComplexBlock :=
  !![complexMatrix8Re A, -complexMatrix8Im A;
     complexMatrix8Im A, complexMatrix8Re A]

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 50000000 in
/-- Sending a complex `8 × 8` matrix to its real block matrix is an
`ℝ`-algebra homomorphism. -/
def complexLinearRealBlock8AlgHom :
    Matrix (Fin 8) (Fin 8) ℂ →ₐ[ℝ] RealMatrix16ComplexBlock where
  toFun := complexLinearRealBlock8
  map_zero' := by
    ext i j u v <;> fin_cases i <;> fin_cases j <;> simp [complexLinearRealBlock8,
      complexMatrix8Re, complexMatrix8Im]
  map_one' := by
    ext i j u v <;> fin_cases i <;> fin_cases j <;>
      by_cases h : u = v <;>
      simp [complexLinearRealBlock8, complexMatrix8Re, complexMatrix8Im,
        Matrix.one_apply, h]
  map_add' A B := by
    ext i j u v <;> fin_cases i <;> fin_cases j <;>
      simp [complexLinearRealBlock8, complexMatrix8Re, complexMatrix8Im] <;>
      ring
  map_mul' A B := by
    ext i j u v <;> fin_cases i <;> fin_cases j <;>
      simp [complexLinearRealBlock8, complexMatrix8Re, complexMatrix8Im, Matrix.mul_apply,
        Fin.sum_univ_two, Fin.sum_univ_eight, Complex.mul_re, Complex.mul_im] <;>
      ring_nf
  commutes' r := by
    ext i j u v <;> fin_cases i <;> fin_cases j <;>
      by_cases h : u = v <;>
      simp [complexLinearRealBlock8, complexMatrix8Re, complexMatrix8Im,
        Matrix.algebraMap_matrix_apply, h]

/-- The real conjugation block on `ℂ⁸`, written in real coordinates. -/
def realMatrix16ConjugationBlock : RealMatrix16ComplexBlock :=
  !![(1 : Matrix (Fin 8) (Fin 8) ℝ), 0; 0, -1]

set_option linter.unnecessarySeqFocus false in
@[simp]
theorem realMatrix16ConjugationBlock_sq :
    realMatrix16ConjugationBlock * realMatrix16ConjugationBlock = 1 := by
  ext i j u v <;> fin_cases i <;> fin_cases j <;>
    simp [realMatrix16ConjugationBlock, Matrix.mul_apply, Fin.sum_univ_two]

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
theorem realMatrix16ConjugationBlock_mul_complexLinearRealBlock8_realCl70ToComplexMatrix8Lin_add
    (v : RealCl07Space) :
    realMatrix16ConjugationBlock * complexLinearRealBlock8 (realCl70ToComplexMatrix8Lin v) +
        complexLinearRealBlock8 (realCl70ToComplexMatrix8Lin v) *
          realMatrix16ConjugationBlock = 0 := by
  ext i j u w <;> fin_cases i <;> fin_cases j <;>
    simp [realMatrix16ConjugationBlock, complexLinearRealBlock8,
      realCl70ToComplexMatrix8Lin, complexMatrix8Re, complexMatrix8Im,
      realMatrix8BlockToComplexMatrix8, realToComplexAlgHom, Matrix.mul_apply,
      Fin.sum_univ_two]

set_option linter.unnecessarySeqFocus false in
/-- The eight-generator real block-matrix model for `Cl(8,0)`. -/
def realCl80ToRealMatrix16ComplexBlockLin :
    RealCl08Space →ₗ[ℝ] RealMatrix16ComplexBlock where
  toFun v := complexLinearRealBlock8 (realCl70ToComplexMatrix8Lin v.1) +
    v.2 • realMatrix16ConjugationBlock
  map_add' x y := by
    ext i j u v <;> fin_cases i <;> fin_cases j <;>
      simp [complexLinearRealBlock8, realCl70ToComplexMatrix8Lin,
        realMatrix16ConjugationBlock, complexMatrix8Re, complexMatrix8Im, map_add,
        add_smul] <;>
      abel
  map_smul' a x := by
    ext i j u v <;> fin_cases i <;> fin_cases j <;>
      simp [complexLinearRealBlock8, realCl70ToComplexMatrix8Lin,
        realMatrix16ConjugationBlock, complexMatrix8Re, complexMatrix8Im, map_smul] <;>
      ring

set_option maxHeartbeats 10000000 in
theorem realCl80ToRealMatrix16ComplexBlockLin_sq (v : RealCl08Space) :
    realCl80ToRealMatrix16ComplexBlockLin v * realCl80ToRealMatrix16ComplexBlockLin v =
      algebraMap ℝ RealMatrix16ComplexBlock (realCl80Form v) := by
  let A := complexLinearRealBlock8 (realCl70ToComplexMatrix8Lin v.1)
  let J := realMatrix16ConjugationBlock
  have hA : A * A = algebraMap ℝ RealMatrix16ComplexBlock (realCl70Form v.1) := by
    change complexLinearRealBlock8AlgHom (realCl70ToComplexMatrix8Lin v.1) *
        complexLinearRealBlock8AlgHom (realCl70ToComplexMatrix8Lin v.1) =
      algebraMap ℝ RealMatrix16ComplexBlock (realCl70Form v.1)
    rw [← map_mul, realCl70ToComplexMatrix8Lin_sq]
    exact complexLinearRealBlock8AlgHom.commutes _
  have hanti : J * A + A * J = 0 := by
    simpa [A, J] using
      realMatrix16ConjugationBlock_mul_complexLinearRealBlock8_realCl70ToComplexMatrix8Lin_add
        v.1
  have hJ : J * J = 1 := by
    simp [J]
  calc
    realCl80ToRealMatrix16ComplexBlockLin v * realCl80ToRealMatrix16ComplexBlockLin v =
        A * A + v.2 • (A * J + J * A) + (v.2 * v.2) • (J * J) := by
      change (A + v.2 • J) * (A + v.2 • J) =
        A * A + v.2 • (A * J + J * A) + (v.2 * v.2) • (J * J)
      rw [mul_add]
      rw [add_mul]
      rw [add_mul]
      rw [mul_smul_comm, smul_mul_assoc, smul_mul_smul_comm]
      rw [smul_add]
      abel
    _ = algebraMap ℝ RealMatrix16ComplexBlock (realCl80Form v) := by
      have hanti' : A * J + J * A = 0 := by simpa [add_comm] using hanti
      rw [hanti', smul_zero, add_zero, hA, hJ]
      rw [Algebra.smul_def, mul_one]
      rw [← map_add]
      congr 1
      obtain ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, h⟩ := v
      simp [realCl80Form, realCl70Form, realCl08Form, realCl07Form, realCl06Form,
        realCl05Form]
      ring

/-- The explicit real block-matrix representation of `Cl(8,0)`. -/
noncomputable def realCl80ToRealMatrix16ComplexBlock :
    CliffordAlgebra realCl80Form →ₐ[ℝ] RealMatrix16ComplexBlock :=
  CliffordAlgebra.lift realCl80Form ⟨realCl80ToRealMatrix16ComplexBlockLin,
    realCl80ToRealMatrix16ComplexBlockLin_sq⟩

@[simp]
theorem realCl80ToRealMatrix16ComplexBlock_ι (v : RealCl08Space) :
    realCl80ToRealMatrix16ComplexBlock (CliffordAlgebra.ι realCl80Form v) =
      realCl80ToRealMatrix16ComplexBlockLin v := by
  simpa [realCl80ToRealMatrix16ComplexBlock] using
    (CliffordAlgebra.lift_ι_apply realCl80ToRealMatrix16ComplexBlockLin
      realCl80ToRealMatrix16ComplexBlockLin_sq v)

/-- Include the first seven positive generators of `Cl(8,0)` as a copy of `Cl(7,0)`. -/
noncomputable def realCl70IntoCl80Lin :
    RealCl07Space →ₗ[ℝ] CliffordAlgebra realCl80Form where
  toFun v := CliffordAlgebra.ι realCl80Form (v, 0)
  map_add' x y := by
    simpa using
      (map_add (CliffordAlgebra.ι realCl80Form) (x, (0 : ℝ)) (y, (0 : ℝ)))
  map_smul' a x := by
    simpa using
      (map_smul (CliffordAlgebra.ι realCl80Form) a (x, (0 : ℝ)))

theorem realCl70IntoCl80Lin_sq (v : RealCl07Space) :
    realCl70IntoCl80Lin v * realCl70IntoCl80Lin v =
      algebraMap ℝ (CliffordAlgebra realCl80Form) (realCl70Form v) := by
  rw [realCl70IntoCl80Lin, LinearMap.coe_mk, AddHom.coe_mk,
    CliffordAlgebra.ι_sq_scalar]
  obtain ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩ := v
  simp [realCl80Form, realCl70Form, realCl08Form, realCl07Form, realCl06Form,
    realCl05Form]

/-- The canonical copy of `Cl(7,0)` inside `Cl(8,0)`. -/
noncomputable def realCl70IntoCl80 :
    CliffordAlgebra realCl70Form →ₐ[ℝ] CliffordAlgebra realCl80Form :=
  CliffordAlgebra.lift realCl70Form ⟨realCl70IntoCl80Lin, realCl70IntoCl80Lin_sq⟩

@[simp]
theorem realCl70IntoCl80_ι (v : RealCl07Space) :
    realCl70IntoCl80 (CliffordAlgebra.ι realCl70Form v) =
      CliffordAlgebra.ι realCl80Form (v, 0) := by
  simpa [realCl70IntoCl80, realCl70IntoCl80Lin] using
    (CliffordAlgebra.lift_ι_apply realCl70IntoCl80Lin realCl70IntoCl80Lin_sq v)

theorem realCl80ToRealMatrix16ComplexBlock_realCl70IntoCl80
    (x : CliffordAlgebra realCl70Form) :
    realCl80ToRealMatrix16ComplexBlock (realCl70IntoCl80 x) =
      complexLinearRealBlock8AlgHom (realCl70ToComplexMatrix8 x) := by
  let F : CliffordAlgebra realCl70Form →ₐ[ℝ] RealMatrix16ComplexBlock :=
    realCl80ToRealMatrix16ComplexBlock.comp realCl70IntoCl80
  let G : CliffordAlgebra realCl70Form →ₐ[ℝ] RealMatrix16ComplexBlock :=
    complexLinearRealBlock8AlgHom.comp realCl70ToComplexMatrix8
  have hFG : F = G := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    simp [F, G, realCl80ToRealMatrix16ComplexBlockLin, complexLinearRealBlock8AlgHom]
  change F x = G x
  rw [hFG]

/-- The eighth positive generator of `Cl(8,0)`. -/
noncomputable def realCl80EighthGenerator : CliffordAlgebra realCl80Form :=
  CliffordAlgebra.ι realCl80Form (0, (1 : ℝ))

set_option linter.unnecessarySeqFocus false in
@[simp]
theorem realCl80ToRealMatrix16ComplexBlock_eighthGenerator :
    realCl80ToRealMatrix16ComplexBlock realCl80EighthGenerator =
      realMatrix16ConjugationBlock := by
  ext i j u v <;> fin_cases i <;> fin_cases j <;>
    simp [realCl80EighthGenerator, realCl80ToRealMatrix16ComplexBlockLin,
      complexLinearRealBlock8, complexMatrix8Re, complexMatrix8Im,
      realMatrix16ConjugationBlock]

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 12000000 in
theorem realMatrix16ComplexBlock_decomposition (A : RealMatrix16ComplexBlock) :
    complexLinearRealBlock8
        (fun i j => (((A 0 0) i j + (A 1 1) i j) / 2 : ℝ) +
          ((((A 1 0) i j - (A 0 1) i j) / 2 : ℝ) * Complex.I)) +
      realMatrix16ConjugationBlock * complexLinearRealBlock8
        (fun i j => (((A 0 0) i j - (A 1 1) i j) / 2 : ℝ) +
          ((-(((A 0 1) i j + (A 1 0) i j) / 2) : ℝ) * Complex.I)) =
      A := by
  ext i j u v <;> fin_cases i <;> fin_cases j <;>
    simp [complexLinearRealBlock8, complexMatrix8Re, complexMatrix8Im,
      realMatrix16ConjugationBlock, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

set_option maxHeartbeats 12000000 in
theorem realCl80ToRealMatrix16ComplexBlock_surjective :
    Function.Surjective realCl80ToRealMatrix16ComplexBlock := by
  intro A
  let C : Matrix (Fin 8) (Fin 8) ℂ :=
    fun i j => (((A 0 0) i j + (A 1 1) i j) / 2 : ℝ) +
      ((((A 1 0) i j - (A 0 1) i j) / 2 : ℝ) * Complex.I)
  let D : Matrix (Fin 8) (Fin 8) ℂ :=
    fun i j => (((A 0 0) i j - (A 1 1) i j) / 2 : ℝ) +
      ((-(((A 0 1) i j + (A 1 0) i j) / 2) : ℝ) * Complex.I)
  rcases realCl70ToComplexMatrix8_surjective C with ⟨x, hx⟩
  rcases realCl70ToComplexMatrix8_surjective D with ⟨y, hy⟩
  refine ⟨realCl70IntoCl80 x + realCl80EighthGenerator * realCl70IntoCl80 y, ?_⟩
  rw [map_add, map_mul, realCl80ToRealMatrix16ComplexBlock_realCl70IntoCl80 x,
    realCl80ToRealMatrix16ComplexBlock_realCl70IntoCl80 y,
    realCl80ToRealMatrix16ComplexBlock_eighthGenerator, hx, hy]
  simpa [C, D] using realMatrix16ComplexBlock_decomposition A

theorem realCl80Clifford_finrank :
    Module.finrank ℝ (CliffordAlgebra realCl80Form) = 256 := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hfin : Module.finrank ℝ RealCl08Space = 8 := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
      Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
      Module.finrank_prod]
    norm_num
  calc
    Module.finrank ℝ (CliffordAlgebra realCl80Form) =
        Module.finrank ℝ (ExteriorAlgebra ℝ RealCl08Space) := by
      exact LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior realCl80Form)
    _ = 2 ^ Module.finrank ℝ RealCl08Space := by
      exact ExteriorAlgebra.finrank_eq_two_pow (K := ℝ)
    _ = 256 := by
      rw [hfin]
      norm_num

theorem realCl80RealMatrix16ComplexBlock_finrank :
    Module.finrank ℝ RealMatrix16ComplexBlock = 256 := by
  rw [Module.finrank_matrix]
  norm_num [Module.finrank_matrix]

theorem realCl80ToRealMatrix16ComplexBlock_injective :
    Function.Injective realCl80ToRealMatrix16ComplexBlock := by
  have hcl_succ : Module.finrank ℝ (CliffordAlgebra realCl80Form) = Nat.succ 255 := by
    simpa using realCl80Clifford_finrank
  letI : FiniteDimensional ℝ (CliffordAlgebra realCl80Form) :=
    FiniteDimensional.of_finrank_eq_succ hcl_succ
  have hdim : Module.finrank ℝ (CliffordAlgebra realCl80Form) =
      Module.finrank ℝ RealMatrix16ComplexBlock := by
    rw [realCl80Clifford_finrank, realCl80RealMatrix16ComplexBlock_finrank]
  simpa using
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := realCl80ToRealMatrix16ComplexBlock.toLinearMap) hdim).mpr
      realCl80ToRealMatrix16ComplexBlock_surjective)

/-- The real Clifford algebra `Cl(8,0)` is the realified complex block matrix algebra. -/
noncomputable def realCl80EquivRealMatrix16ComplexBlock :
    CliffordAlgebra realCl80Form ≃ₐ[ℝ] RealMatrix16ComplexBlock :=
  AlgEquiv.ofBijective realCl80ToRealMatrix16ComplexBlock
    ⟨realCl80ToRealMatrix16ComplexBlock_injective,
      realCl80ToRealMatrix16ComplexBlock_surjective⟩

/-- The canonical equivalence from the realified complex `2 × 2` block presentation to the
ordinary `16 × 16` matrix algebra. -/
noncomputable def realMatrix16ComplexBlockEquivMatrix16 :
    RealMatrix16ComplexBlock ≃ₐ[ℝ] Matrix (Fin 16) (Fin 16) ℝ :=
  (Matrix.compAlgEquiv (Fin 2) (Fin 8) ℝ ℝ).trans
    (Matrix.reindexAlgEquiv ℝ ℝ (finProdFinEquiv : Fin 2 × Fin 8 ≃ Fin (2 * 8)))

/-- The real Clifford algebra `Cl(8,0)` is the full `16 × 16` real matrix algebra. -/
noncomputable def realCl80EquivRealMatrix16 :
    CliffordAlgebra realCl80Form ≃ₐ[ℝ] Matrix (Fin 16) (Fin 16) ℝ :=
  realCl80EquivRealMatrix16ComplexBlock.trans realMatrix16ComplexBlockEquivMatrix16

namespace RealClassification

/-- Canonical quadratic form for the even algebra `Cl⁺(7,0)` in the
real-classification namespace. -/
noncomputable abbrev Q_7_0 :
    QuadraticForm ℝ ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) :=
  realCl70Form

/-- Canonical even real-classification entry: `Cl⁺(7,0) ≃ Mat₈(ℝ)`. -/
noncomputable def cl_7_0_even_equivMatrix8 :
    CliffordAlgebra.even Q_7_0 ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ := by
  simpa [Q_7_0] using realEvenCl70EquivRealMatrix8

/-- Canonical real-classification entry: `Cl(7,0) ≃ Mat₈(ℂ)`. -/
noncomputable def cl_7_0_equivComplexMatrix8 :
    CliffordAlgebra Q_7_0 ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℂ := by
  simpa [Q_7_0] using realCl70EquivComplexMatrix8

/-- Canonical quadratic form for the even algebra `Cl⁺(8,0)` in the
real-classification namespace. -/
noncomputable abbrev Q_8_0 :
    QuadraticForm ℝ (((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) :=
  realCl80Form

/-- Canonical even real-classification entry:
`Cl⁺(8,0) ≃ Mat₈(ℝ) × Mat₈(ℝ)`. -/
noncomputable def cl_8_0_even_equivMatrix8Prod :
    CliffordAlgebra.even Q_8_0 ≃ₐ[ℝ]
      Matrix (Fin 8) (Fin 8) ℝ × Matrix (Fin 8) (Fin 8) ℝ := by
  simpa [Q_8_0] using realEvenCl80EquivRealMatrix8Prod

/-- Canonical real-classification entry: `Cl(8,0) ≃ Mat₁₆(ℝ)`. -/
noncomputable def cl_8_0_equivMatrix16 :
    CliffordAlgebra Q_8_0 ≃ₐ[ℝ] Matrix (Fin 16) (Fin 16) ℝ := by
  simpa [Q_8_0] using realCl80EquivRealMatrix16

end RealClassification

end

end Spinor
