import Spinor.LowDimensional
import Mathlib.Algebra.QuaternionBasis

/-!
  Classical identification of the negative-signature real Clifford algebra
  `Cl(0,3) ≃ ℍ × ℍ` over `ℝ`.

  This is the last missing algebraic step before `Spin(4) ≃ Sp(1) × Sp(1)`:
  composed with `realEvenCl04EquivCl03` in `Spinor.LowDimensional`, it yields
  `Cl⁺(0,4) ≃ ℍ × ℍ`.

  Writing `e₁, e₂, e₃` for the three generators of `Cl(0,3)`, the pseudoscalar
  `ω := e₁ e₂ e₃` is central and satisfies `ω² = 1`. The forward map is
  obtained from the Clifford universal property using two quaternion-valued
  lifts that differ by the sign of `e₃`; the inverse is an explicit linear
  combination involving the central idempotents `p± := (1 ± ω)/2`.
-/

namespace Spinor

namespace Cl03QuaternionProd

noncomputable section

open scoped Quaternion
open CliffordAlgebra

/-- Shorthand for the Hamilton quaternion algebra type used throughout this file. -/
local notation "H" => ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]

/-- First generator of `Cl(0,3)` (image of `e₁`). -/
def e1 : CliffordAlgebra realCl03Form := ι realCl03Form ((1, 0), 0)

/-- Second generator of `Cl(0,3)` (image of `e₂`). -/
def e2 : CliffordAlgebra realCl03Form := ι realCl03Form ((0, 1), 0)

/-- Third generator of `Cl(0,3)` (image of `e₃`). -/
def e3 : CliffordAlgebra realCl03Form := ι realCl03Form ((0, 0), 1)

/-- Value of the 3-form: `Q((a, b), c) = -(a² + b² + c²)`. -/
@[simp]
lemma realCl03Form_apply (a b c : ℝ) :
    realCl03Form ((a, b), c) = -(a * a + b * b + c * c) := by
  simp [realCl03Form]
  ring

/-- `e₁² = -1` in `Cl(0,3)`. -/
lemma e1_mul_e1 : e1 * e1 = -1 := by
  simp [e1, ι_sq_scalar, Algebra.algebraMap_eq_smul_one]

/-- `e₂² = -1` in `Cl(0,3)`. -/
lemma e2_mul_e2 : e2 * e2 = -1 := by
  simp [e2, ι_sq_scalar, Algebra.algebraMap_eq_smul_one]

/-- `e₃² = -1` in `Cl(0,3)`. -/
lemma e3_mul_e3 : e3 * e3 = -1 := by
  simp [e3, ι_sq_scalar, Algebra.algebraMap_eq_smul_one]

/-- Basis vectors `e₁` and `e₂` anticommute. -/
lemma e2_mul_e1 : e2 * e1 = -(e1 * e2) := by
  have hp : QuadraticMap.polar realCl03Form ((1, 0), 0) ((0, 1), 0) = 0 := by
    simp [QuadraticMap.polar]
  have h := CliffordAlgebra.ι_mul_ι_add_swap
    (Q := realCl03Form) ((1, 0), 0) ((0, 1), 0)
  rw [hp, map_zero] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)

/-- Basis vectors `e₁` and `e₃` anticommute. -/
lemma e3_mul_e1 : e3 * e1 = -(e1 * e3) := by
  have hp : QuadraticMap.polar realCl03Form ((1, 0), 0) ((0, 0), 1) = 0 := by
    simp [QuadraticMap.polar]
  have h := CliffordAlgebra.ι_mul_ι_add_swap
    (Q := realCl03Form) ((1, 0), 0) ((0, 0), 1)
  rw [hp, map_zero] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)

/-- Basis vectors `e₂` and `e₃` anticommute. -/
lemma e3_mul_e2 : e3 * e2 = -(e2 * e3) := by
  have hp : QuadraticMap.polar realCl03Form ((0, 1), 0) ((0, 0), 1) = 0 := by
    simp [QuadraticMap.polar]
  have h := CliffordAlgebra.ι_mul_ι_add_swap
    (Q := realCl03Form) ((0, 1), 0) ((0, 0), 1)
  rw [hp, map_zero] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)

/-- Linear map `((a,b), c) ↦ a·i + b·j + (εc)·k` into `ℍ = ℍ[ℝ, -1, 0, -1]`. -/
def toHLin (ε : ℝ) : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] H where
  toFun p := ⟨0, p.1.1, p.1.2, ε * p.2⟩
  map_add' x y := by
    cases x with | mk x₁ x₂ =>
    cases y with | mk y₁ y₂ =>
    cases x₁ with | mk x₁a x₁b =>
    cases y₁ with | mk y₁a y₁b =>
    ext <;> simp
    ring
  map_smul' r x := by
    cases x with | mk x₁ x₂ =>
    cases x₁ with | mk x₁a x₁b =>
    ext <;> simp
    ring

@[simp] lemma toHLin_apply (ε a b c : ℝ) :
    toHLin ε ((a, b), c) = ⟨0, a, b, ε * c⟩ := rfl

/-- `(toHLin ε v)² = Q(v) • 1` when `ε² = 1`. -/
lemma toHLin_sq (ε : ℝ) (hε : ε * ε = 1) (v : (ℝ × ℝ) × ℝ) :
    toHLin ε v * toHLin ε v = algebraMap ℝ H (realCl03Form v) := by
  obtain ⟨⟨a, b⟩, c⟩ := v
  simp only [toHLin_apply, realCl03Form_apply]
  ext <;> simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;>
    (try linear_combination (-(c * c)) * hε) <;>
    ring

/-- Forward `AlgHom` out of `Cl(0,3)`, parametrised by sign `ε ∈ {±1}` applied to `e₃`. -/
noncomputable def toH (ε : ℝ) (hε : ε * ε = 1) :
    CliffordAlgebra realCl03Form →ₐ[ℝ] H :=
  CliffordAlgebra.lift realCl03Form ⟨toHLin ε, toHLin_sq ε hε⟩

@[simp] lemma toH_e1 (ε : ℝ) (hε : ε * ε = 1) :
    toH ε hε e1 = ⟨0, 1, 0, 0⟩ := by
  unfold toH e1
  rw [CliffordAlgebra.lift_ι_apply]
  show toHLin ε ((1, 0), 0) = _
  ext <;> simp

@[simp] lemma toH_e2 (ε : ℝ) (hε : ε * ε = 1) :
    toH ε hε e2 = ⟨0, 0, 1, 0⟩ := by
  unfold toH e2
  rw [CliffordAlgebra.lift_ι_apply]
  show toHLin ε ((0, 1), 0) = _
  ext <;> simp

@[simp] lemma toH_e3 (ε : ℝ) (hε : ε * ε = 1) :
    toH ε hε e3 = ⟨0, 0, 0, ε⟩ := by
  unfold toH e3
  rw [CliffordAlgebra.lift_ι_apply]
  show toHLin ε ((0, 0), 1) = _
  ext <;> simp

@[simp] lemma toH_ι (ε : ℝ) (hε : ε * ε = 1) (a b c : ℝ) :
    toH ε hε (ι realCl03Form ((a, b), c)) = ⟨0, a, b, ε * c⟩ := by
  unfold toH
  rw [CliffordAlgebra.lift_ι_apply]
  ext <;> simp [toHLin_apply]

/-- Forward map `Cl(0,3) → ℍ × ℍ`: paired lifts differing by sign on `e₃`. -/
noncomputable def toQuatPair : CliffordAlgebra realCl03Form →ₐ[ℝ] H × H :=
  (toH 1 (by ring)).prod (toH (-1) (by ring))

@[simp] lemma toQuatPair_e1 :
    toQuatPair e1 = (⟨0, 1, 0, 0⟩, ⟨0, 1, 0, 0⟩) := by
  simp [toQuatPair]

@[simp] lemma toQuatPair_e2 :
    toQuatPair e2 = (⟨0, 0, 1, 0⟩, ⟨0, 0, 1, 0⟩) := by
  simp [toQuatPair]

@[simp] lemma toQuatPair_e3 :
    toQuatPair e3 = (⟨0, 0, 0, 1⟩, ⟨0, 0, 0, -1⟩) := by
  simp [toQuatPair]

/-! ### The pseudoscalar `ω := e₁ e₂ e₃` -/

/-- The pseudoscalar element. -/
def ω : CliffordAlgebra realCl03Form := e1 * e2 * e3

/-- `e₁ e₂ e₁ = e₂`. -/
lemma e1_e2_e1 : e1 * e2 * e1 = e2 := by
  rw [mul_assoc, e2_mul_e1, mul_neg, ← mul_assoc, e1_mul_e1, neg_one_mul, neg_neg]

/-- `e₁ e₃ e₁ = e₃`. -/
lemma e1_e3_e1 : e1 * e3 * e1 = e3 := by
  rw [mul_assoc, e3_mul_e1, mul_neg, ← mul_assoc, e1_mul_e1, neg_one_mul, neg_neg]

/-- `e₂ e₃ e₂ = e₃`. -/
lemma e2_e3_e2 : e2 * e3 * e2 = e3 := by
  rw [mul_assoc, e3_mul_e2, mul_neg, ← mul_assoc, e2_mul_e2, neg_one_mul, neg_neg]

lemma ω_e1 : ω * e1 = -(e2 * e3) := by
  show e1 * e2 * e3 * e1 = -(e2 * e3)
  rw [mul_assoc (e1 * e2) e3 e1, e3_mul_e1, mul_neg, mul_assoc e1 e2 _,
      ← mul_assoc e2 e1 e3, e2_mul_e1, neg_mul, mul_neg, neg_neg,
      ← mul_assoc e1 (e1 * e2) e3, ← mul_assoc e1 e1 e2,
      e1_mul_e1, neg_one_mul]
  exact neg_mul e2 e3

lemma e1_ω : e1 * ω = -(e2 * e3) := by
  show e1 * (e1 * e2 * e3) = -(e2 * e3)
  rw [← mul_assoc, ← mul_assoc, e1_mul_e1, neg_one_mul]
  exact neg_mul e2 e3

lemma ω_e2 : ω * e2 = e1 * e3 := by
  show e1 * e2 * e3 * e2 = e1 * e3
  rw [mul_assoc (e1 * e2) e3 e2, e3_mul_e2, mul_neg, mul_assoc e1 e2 _,
      ← mul_assoc e2 e2 e3, e2_mul_e2, neg_one_mul, mul_neg, neg_neg]

lemma e2_ω : e2 * ω = e1 * e3 := by
  show e2 * (e1 * e2 * e3) = e1 * e3
  rw [← mul_assoc, ← mul_assoc, e2_mul_e1, neg_mul, mul_assoc e1 e2 e2,
      e2_mul_e2, mul_neg, mul_one, neg_neg]

lemma ω_e3 : ω * e3 = -(e1 * e2) := by
  show e1 * e2 * e3 * e3 = -(e1 * e2)
  rw [mul_assoc (e1 * e2) e3 e3, e3_mul_e3, mul_neg, mul_one]

lemma e3_ω : e3 * ω = -(e1 * e2) := by
  show e3 * (e1 * e2 * e3) = -(e1 * e2)
  rw [← mul_assoc e3 (e1 * e2) e3, ← mul_assoc e3 e1 e2, e3_mul_e1,
      neg_mul, mul_assoc e1 e3 e2, e3_mul_e2, mul_neg, neg_neg,
      mul_assoc e1 (e2 * e3) e3, mul_assoc e2 e3 e3, e3_mul_e3,
      mul_neg_one, mul_neg]

/-- The pseudoscalar `ω` commutes with `e₁`. -/
lemma ω_comm_e1 : ω * e1 = e1 * ω := by rw [ω_e1, e1_ω]

/-- The pseudoscalar `ω` commutes with `e₂`. -/
lemma ω_comm_e2 : ω * e2 = e2 * ω := by rw [ω_e2, e2_ω]

/-- The pseudoscalar `ω` commutes with `e₃`. -/
lemma ω_comm_e3 : ω * e3 = e3 * ω := by rw [ω_e3, e3_ω]

/-- `ω² = 1`. -/
lemma ω_sq : ω * ω = 1 := by
  show ω * (e1 * e2 * e3) = 1
  rw [← mul_assoc ω (e1 * e2) e3, ← mul_assoc ω e1 e2, ω_e1, neg_mul, neg_mul,
      e2_e3_e2, e3_mul_e3, neg_neg]

/-! ### Idempotents `p± := (1 ± ω)/2` -/

/-- Positive pseudoscalar idempotent `p₊ := (1 + ω)/2`. -/
def pPlus : CliffordAlgebra realCl03Form := (2⁻¹ : ℝ) • (1 + ω)

/-- Negative pseudoscalar idempotent `p₋ := (1 - ω)/2`. -/
def pMinus : CliffordAlgebra realCl03Form := (2⁻¹ : ℝ) • (1 - ω)

/-- `p₊ + p₋ = 1`. -/
lemma pPlus_add_pMinus : pPlus + pMinus = 1 := by
  show (2⁻¹ : ℝ) • (1 + ω) + (2⁻¹ : ℝ) • (1 - ω) = 1
  rw [← smul_add,
      show (1 + ω) + (1 - ω) = (2 : ℝ) • (1 : CliffordAlgebra realCl03Form) from by
        rw [two_smul]; abel,
      smul_smul]
  simp

/-- `ω * p₊ = p₊`. -/
lemma ω_mul_pPlus : ω * pPlus = pPlus := by
  show ω * ((2⁻¹ : ℝ) • (1 + ω)) = (2⁻¹ : ℝ) • (1 + ω)
  rw [Algebra.mul_smul_comm, mul_add, mul_one, show ω * ω = 1 from ω_sq, add_comm]

/-- `ω * p₋ = -p₋`. -/
lemma ω_mul_pMinus : ω * pMinus = -pMinus := by
  show ω * ((2⁻¹ : ℝ) • (1 - ω)) = -((2⁻¹ : ℝ) • (1 - ω))
  rw [Algebra.mul_smul_comm, mul_sub, mul_one, show ω * ω = 1 from ω_sq,
      ← smul_neg, neg_sub]

/-- `p₊ * ω = p₊`. -/
lemma pPlus_mul_ω : pPlus * ω = pPlus := by
  show ((2⁻¹ : ℝ) • (1 + ω)) * ω = (2⁻¹ : ℝ) • (1 + ω)
  rw [Algebra.smul_mul_assoc, add_mul, one_mul, show ω * ω = 1 from ω_sq, add_comm]

/-- `p₋ * ω = -p₋`. -/
lemma pMinus_mul_ω : pMinus * ω = -pMinus := by
  show ((2⁻¹ : ℝ) • (1 - ω)) * ω = -((2⁻¹ : ℝ) • (1 - ω))
  rw [Algebra.smul_mul_assoc, sub_mul, one_mul, show ω * ω = 1 from ω_sq,
      ← smul_neg, neg_sub]

/-- `p₊² = p₊`. -/
lemma pPlus_sq : pPlus * pPlus = pPlus := by
  show ((2⁻¹ : ℝ) • (1 + ω)) * pPlus = pPlus
  rw [Algebra.smul_mul_assoc, add_mul, one_mul, ω_mul_pPlus, ← two_smul ℝ pPlus,
      smul_smul]
  simp

/-- `p₋² = p₋`. -/
lemma pMinus_sq : pMinus * pMinus = pMinus := by
  show ((2⁻¹ : ℝ) • (1 - ω)) * pMinus = pMinus
  rw [Algebra.smul_mul_assoc, sub_mul, one_mul, ω_mul_pMinus, sub_neg_eq_add,
      ← two_smul ℝ pMinus, smul_smul]
  simp

/-- `p₊ * p₋ = 0`. -/
lemma pPlus_mul_pMinus : pPlus * pMinus = 0 := by
  show ((2⁻¹ : ℝ) • (1 + ω)) * pMinus = 0
  rw [Algebra.smul_mul_assoc, add_mul, one_mul, ω_mul_pMinus, add_neg_cancel,
      smul_zero]

/-- `p₋ * p₊ = 0`. -/
lemma pMinus_mul_pPlus : pMinus * pPlus = 0 := by
  show ((2⁻¹ : ℝ) • (1 - ω)) * pPlus = 0
  rw [Algebra.smul_mul_assoc, sub_mul, one_mul, ω_mul_pPlus, sub_self, smul_zero]

/-! ### Quaternion embedding via the pair `(e₁, e₂)` -/

/-- Quaternion basis inside `Cl(0,3)` given by `i := e₁, j := e₂, k := e₁ e₂`. -/
noncomputable def cl03QuaternionBasis :
    QuaternionAlgebra.Basis (CliffordAlgebra realCl03Form) (-1 : ℝ) (0 : ℝ) (-1 : ℝ) where
  i := e1
  j := e2
  k := e1 * e2
  i_mul_i := by rw [e1_mul_e1]; simp
  j_mul_j := by rw [e2_mul_e2]; simp
  i_mul_j := rfl
  j_mul_i := by rw [e2_mul_e1]; simp

/-- Embedding `H → Cl(0,3)` sending `i ↦ e₁`, `j ↦ e₂`, `k ↦ e₁ e₂`. -/
noncomputable def embH : H →ₐ[ℝ] CliffordAlgebra realCl03Form :=
  cl03QuaternionBasis.liftHom

@[simp] lemma embH_i : embH ⟨0, 1, 0, 0⟩ = e1 := by
  simp [embH, QuaternionAlgebra.Basis.lift, cl03QuaternionBasis]

@[simp] lemma embH_j : embH ⟨0, 0, 1, 0⟩ = e2 := by
  simp [embH, QuaternionAlgebra.Basis.lift, cl03QuaternionBasis]

@[simp] lemma embH_k : embH ⟨0, 0, 0, 1⟩ = e1 * e2 := by
  simp [embH, QuaternionAlgebra.Basis.lift, cl03QuaternionBasis]

/-! ### `ω` is central; the idempotents `p±` commute with every element -/

/-- `ω` commutes with `e₁ e₂`. -/
lemma ω_comm_e1e2 : ω * (e1 * e2) = (e1 * e2) * ω := by
  rw [← mul_assoc, ω_comm_e1, mul_assoc, ω_comm_e2, ← mul_assoc]

private lemma ι_decomp (a b c : ℝ) :
    ι realCl03Form ((a, b), c) = a • e1 + b • e2 + c • e3 := by
  have hdec : ((a, b), c)
      = a • ((1, 0), (0 : ℝ)) + b • ((0, 1), (0 : ℝ)) + c • (((0 : ℝ), 0), 1) := by
    ext <;> simp
  rw [hdec, map_add, map_add, map_smul, map_smul, map_smul]
  rfl

@[simp] lemma toQuatPair_ι (a b c : ℝ) :
    toQuatPair (ι realCl03Form ((a, b), c)) =
      ((⟨0, a, b, c⟩ : H), (⟨0, a, b, -c⟩ : H)) := by
  rw [ι_decomp]
  ext <;> simp [toQuatPair]

/-- `ω` is central: it commutes with every element of `Cl(0,3)`. -/
lemma ω_central (x : CliffordAlgebra realCl03Form) : ω * x = x * ω := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r ω).symm
  | ι v =>
    obtain ⟨⟨a, b⟩, c⟩ := v
    rw [ι_decomp]
    simp only [mul_add, add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      ω_comm_e1, ω_comm_e2, ω_comm_e3]
  | mul x y hx hy =>
    rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

/-- `p₊` commutes with every element. -/
lemma pPlus_comm (x : CliffordAlgebra realCl03Form) : pPlus * x = x * pPlus := by
  show ((2⁻¹ : ℝ) • (1 + ω)) * x = x * ((2⁻¹ : ℝ) • (1 + ω))
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, add_mul, mul_add,
      one_mul, mul_one, ω_central]

/-- `p₋` commutes with every element. -/
lemma pMinus_comm (x : CliffordAlgebra realCl03Form) : pMinus * x = x * pMinus := by
  show ((2⁻¹ : ℝ) • (1 - ω)) * x = x * ((2⁻¹ : ℝ) • (1 - ω))
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, sub_mul, mul_sub,
      one_mul, mul_one, ω_central]

/-! ### The inverse map `ℍ × ℍ →ₐ[ℝ] Cl(0,3)` -/

private lemma mul_pMinus_mul_pMinus (x y : CliffordAlgebra realCl03Form) :
    (x * pMinus) * (y * pMinus) = x * y * pMinus := by
  rw [mul_assoc x pMinus, ← mul_assoc pMinus y pMinus, pMinus_comm y,
      mul_assoc y pMinus pMinus, pMinus_sq, ← mul_assoc x y pMinus]

private lemma mul_pPlus_mul_pPlus (x y : CliffordAlgebra realCl03Form) :
    (x * pPlus) * (y * pPlus) = x * y * pPlus := by
  rw [mul_assoc x pPlus, ← mul_assoc pPlus y pPlus, pPlus_comm y,
      mul_assoc y pPlus pPlus, pPlus_sq, ← mul_assoc x y pPlus]

private lemma mul_pMinus_mul_pPlus (x y : CliffordAlgebra realCl03Form) :
    (x * pMinus) * (y * pPlus) = 0 := by
  rw [mul_assoc x pMinus, ← mul_assoc pMinus y pPlus, pMinus_comm y,
      mul_assoc y pMinus pPlus, pMinus_mul_pPlus, mul_zero, mul_zero]

private lemma mul_pPlus_mul_pMinus (x y : CliffordAlgebra realCl03Form) :
    (x * pPlus) * (y * pMinus) = 0 := by
  rw [mul_assoc x pPlus, ← mul_assoc pPlus y pMinus, pPlus_comm y,
      mul_assoc y pPlus pMinus, pPlus_mul_pMinus, mul_zero, mul_zero]

/-- Underlying linear map of `ofQuatPair`. -/
def ofQuatPairLin : H × H →ₗ[ℝ] CliffordAlgebra realCl03Form where
  toFun p := embH p.1 * pMinus + embH p.2 * pPlus
  map_add' p q := by
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    show embH (a + c) * pMinus + embH (b + d) * pPlus
        = (embH a * pMinus + embH b * pPlus) + (embH c * pMinus + embH d * pPlus)
    rw [map_add, map_add, add_mul, add_mul]
    abel
  map_smul' r p := by
    obtain ⟨a, b⟩ := p
    show embH (r • a) * pMinus + embH (r • b) * pPlus
        = r • (embH a * pMinus + embH b * pPlus)
    rw [map_smul, map_smul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, smul_add]

@[simp] lemma ofQuatPairLin_apply (p : H × H) :
    ofQuatPairLin p = embH p.1 * pMinus + embH p.2 * pPlus := rfl

/-- Inverse map `ℍ × ℍ →ₐ[ℝ] Cl(0,3)`: `(q, r) ↦ embH q · p₋ + embH r · p₊`. -/
noncomputable def ofQuatPair : H × H →ₐ[ℝ] CliffordAlgebra realCl03Form :=
  AlgHom.ofLinearMap ofQuatPairLin
    (by
      show embH (1 : H) * pMinus + embH (1 : H) * pPlus = 1
      rw [map_one, one_mul, one_mul, add_comm, pPlus_add_pMinus])
    (fun p q => by
      obtain ⟨a, b⟩ := p
      obtain ⟨c, d⟩ := q
      show embH (a * c) * pMinus + embH (b * d) * pPlus
          = (embH a * pMinus + embH b * pPlus) * (embH c * pMinus + embH d * pPlus)
      rw [map_mul, map_mul, add_mul, mul_add, mul_add,
          mul_pMinus_mul_pMinus, mul_pMinus_mul_pPlus,
          mul_pPlus_mul_pMinus, mul_pPlus_mul_pPlus]
      abel)

@[simp] lemma ofQuatPair_apply (p : H × H) :
    ofQuatPair p = embH p.1 * pMinus + embH p.2 * pPlus := rfl

/-! ### Round-trip identities and the final equivalence -/

/-- `(e₁ e₂)² = -1`. -/
lemma e1e2_sq : (e1 * e2) * (e1 * e2) = -1 := by
  rw [← mul_assoc (e1 * e2) e1 e2, e1_e2_e1, e2_mul_e2]

/-- `e₁ e₂ · ω = -e₃`. -/
lemma e1e2_mul_ω : e1 * e2 * ω = -e3 := by
  show e1 * e2 * (e1 * e2 * e3) = -e3
  rw [← mul_assoc (e1 * e2) (e1 * e2) e3, e1e2_sq, neg_one_mul]

@[simp] lemma embH_neg_k : embH ⟨0, 0, 0, -1⟩ = -(e1 * e2) := by
  have h : (⟨0, 0, 0, -1⟩ : H) = -⟨0, 0, 0, 1⟩ := by ext <;> simp
  rw [h, map_neg, embH_k]

/-- `p₋ - p₊ = -ω`. -/
lemma pMinus_sub_pPlus : pMinus - pPlus = -ω := by
  show (2⁻¹ : ℝ) • (1 - ω) - (2⁻¹ : ℝ) • (1 + ω) = -ω
  rw [← smul_sub,
      show (1 - ω) - (1 + ω) = -((2 : ℝ) • ω) from by rw [two_smul]; abel,
      smul_neg, smul_smul]
  simp

/-- `toH ε ω = algebraMap ℝ H (-ε)`. -/
@[simp] lemma toH_ω (ε : ℝ) (hε : ε * ε = 1) :
    toH ε hε ω = algebraMap ℝ H (-ε) := by
  show toH ε hε (e1 * e2 * e3) = _
  rw [map_mul, map_mul, toH_e1, toH_e2, toH_e3]
  ext <;> simp [Algebra.algebraMap_eq_smul_one]

@[simp] lemma toH_one_pPlus : toH 1 (by ring) pPlus = 0 := by
  show toH 1 (by ring) ((2⁻¹ : ℝ) • (1 + ω)) = 0
  rw [map_smul, map_add, map_one, toH_ω]
  ext <;> simp [Algebra.algebraMap_eq_smul_one]

@[simp] lemma toH_one_pMinus : toH 1 (by ring) pMinus = 1 := by
  show toH 1 (by ring) ((2⁻¹ : ℝ) • (1 - ω)) = 1
  rw [map_smul, map_sub, map_one, toH_ω]
  ext <;> simp [Algebra.algebraMap_eq_smul_one]
  norm_num

@[simp] lemma toH_neg_one_pPlus : toH (-1) (by ring) pPlus = 1 := by
  show toH (-1) (by ring) ((2⁻¹ : ℝ) • (1 + ω)) = 1
  rw [map_smul, map_add, map_one, toH_ω]
  ext <;> simp [Algebra.algebraMap_eq_smul_one]
  norm_num

@[simp] lemma toH_neg_one_pMinus : toH (-1) (by ring) pMinus = 0 := by
  show toH (-1) (by ring) ((2⁻¹ : ℝ) • (1 - ω)) = 0
  rw [map_smul, map_sub, map_one, toH_ω]
  ext <;> simp [Algebra.algebraMap_eq_smul_one]

/-- `(toH ε).comp embH = id`. -/
lemma toH_comp_embH (ε : ℝ) (hε : ε * ε = 1) :
    (toH ε hε).comp embH = AlgHom.id ℝ H := by
  apply QuaternionAlgebra.hom_ext
  · show (toH ε hε).comp embH ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩
    rw [AlgHom.comp_apply, embH_i, toH_e1]
  · show (toH ε hε).comp embH ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩
    rw [AlgHom.comp_apply, embH_j, toH_e2]

@[simp] lemma toH_embH (ε : ℝ) (hε : ε * ε = 1) (q : H) :
    toH ε hε (embH q) = q :=
  AlgHom.ext_iff.mp (toH_comp_embH ε hε) q

/-- Forward map followed by backward map is the identity on generators. -/
@[simp] lemma ofQuatPair_toQuatPair_e1 : ofQuatPair (toQuatPair e1) = e1 := by
  rw [toQuatPair_e1, ofQuatPair_apply, embH_i]
  show e1 * pMinus + e1 * pPlus = e1
  rw [← mul_add, add_comm pMinus pPlus, pPlus_add_pMinus, mul_one]

@[simp] lemma ofQuatPair_toQuatPair_e2 : ofQuatPair (toQuatPair e2) = e2 := by
  rw [toQuatPair_e2, ofQuatPair_apply, embH_j]
  show e2 * pMinus + e2 * pPlus = e2
  rw [← mul_add, add_comm pMinus pPlus, pPlus_add_pMinus, mul_one]

@[simp] lemma ofQuatPair_toQuatPair_e3 : ofQuatPair (toQuatPair e3) = e3 := by
  rw [toQuatPair_e3, ofQuatPair_apply, embH_k, embH_neg_k, neg_mul,
      ← mul_neg, ← mul_add,
      show pMinus + -pPlus = -ω from by rw [← sub_eq_add_neg]; exact pMinus_sub_pPlus,
      mul_neg, e1e2_mul_ω, neg_neg]

/-- `ofQuatPair ∘ toQuatPair = id`. -/
lemma ofQuatPair_comp_toQuatPair :
    ofQuatPair.comp toQuatPair = AlgHom.id ℝ (CliffordAlgebra realCl03Form) := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  obtain ⟨⟨a, b⟩, c⟩ := v
  show ofQuatPair (toQuatPair (ι realCl03Form ((a, b), c))) = ι realCl03Form ((a, b), c)
  rw [ι_decomp]
  simp only [map_add, map_smul, ofQuatPair_toQuatPair_e1, ofQuatPair_toQuatPair_e2,
    ofQuatPair_toQuatPair_e3]

/-- Backward map followed by forward map is the identity on `ℍ × ℍ`. -/
lemma toQuatPair_comp_ofQuatPair :
    toQuatPair.comp ofQuatPair = AlgHom.id ℝ (H × H) := by
  apply AlgHom.ext
  rintro ⟨q, r⟩
  show toQuatPair (ofQuatPair (q, r)) = (q, r)
  rw [ofQuatPair_apply, map_add, map_mul, map_mul]
  simp only [toQuatPair, AlgHom.prod_apply, toH_embH, toH_one_pMinus, toH_neg_one_pMinus,
    toH_one_pPlus, toH_neg_one_pPlus, Prod.mk_mul_mk, Prod.mk_add_mk,
    mul_one, mul_zero, add_zero, zero_add]

/-- **Main result**: the negative-signature real Clifford algebra `Cl(0,3)` is
    isomorphic (as an `ℝ`-algebra) to the direct product `ℍ × ℍ`. -/
noncomputable def realCl03EquivQuaternionProd :
    CliffordAlgebra realCl03Form ≃ₐ[ℝ] H × H :=
  AlgEquiv.ofAlgHom toQuatPair ofQuatPair
    toQuatPair_comp_ofQuatPair
    ofQuatPair_comp_toQuatPair

@[simp] theorem realCl03EquivQuaternionProd_apply_star (x : CliffordAlgebra realCl03Form) :
    realCl03EquivQuaternionProd (star x) = star (realCl03EquivQuaternionProd x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      ext <;> simp [realCl03EquivQuaternionProd]
  | ι v =>
      obtain ⟨⟨a, b⟩, c⟩ := v
      ext <;> simp [realCl03EquivQuaternionProd, CliffordAlgebra.star_def]
  | mul a b ha hb =>
      simp [ha, hb]
  | add a b ha hb =>
      simp [ha, hb]

end

end Cl03QuaternionProd

open scoped Quaternion
local notation "H" => ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]

/-- The even real Clifford algebra `Cl⁺(0,4)` is isomorphic to `ℍ × ℍ`.

This composes `realEvenCl04EquivCl03 : Cl⁺(0,4) ≃ Cl(0,3)` (from
`Spinor.LowDimensional`) with `Cl03QuaternionProd.realCl03EquivQuaternionProd :
Cl(0,3) ≃ ℍ × ℍ`. It is the classical Bott-period entry
`Cl⁺(0,4) ≃ ℍ ⊕ ℍ` and the algebraic core of `Spin(4) ≃ Sp(1) × Sp(1)`. -/
noncomputable def realEvenCl04EquivQuaternionProd :
    CliffordAlgebra.even realCl04Form ≃ₐ[ℝ]
      H × H :=
  realEvenCl04EquivCl03.trans Cl03QuaternionProd.realCl03EquivQuaternionProd

set_option linter.unnecessarySeqFocus false in
/-- The generator map for the explicit `Cl(0,4) ≃ Mat₂(ℍ)` model. -/
def realCl04ToQuaternionMatrixLin :
    (((ℝ × ℝ) × ℝ) × ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) H where
  toFun v := !![⟨0, v.1.1.1, v.1.1.2, v.1.2⟩, (v.2 : H);
      -(v.2 : H), ⟨0, -v.1.1.1, -v.1.1.2, -v.1.2⟩]
  map_add' x y := by
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := x
    obtain ⟨⟨⟨e, f⟩, g⟩, h⟩ := y
    ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' a x := by
    obtain ⟨⟨⟨b, c⟩, d⟩, e⟩ := x
    ext i j <;> fin_cases i <;> fin_cases j <;> simp

set_option linter.unnecessarySeqFocus false in
theorem realCl04ToQuaternionMatrixLin_sq (v : (((ℝ × ℝ) × ℝ) × ℝ)) :
    realCl04ToQuaternionMatrixLin v * realCl04ToQuaternionMatrixLin v =
      algebraMap ℝ (Matrix (Fin 2) (Fin 2) H) (realCl04Form v) := by
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := v
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [realCl04ToQuaternionMatrixLin, Matrix.mul_apply, Matrix.algebraMap_matrix_apply,
      QuaternionAlgebra.mk_mul_mk] <;>
    ring_nf

/-- The explicit quaternionic matrix representation of the real Clifford algebra `Cl(0,4)`. -/
noncomputable def realCl04ToQuaternionMatrix :
    CliffordAlgebra realCl04Form →ₐ[ℝ] Matrix (Fin 2) (Fin 2) H :=
  CliffordAlgebra.lift realCl04Form ⟨realCl04ToQuaternionMatrixLin,
    realCl04ToQuaternionMatrixLin_sq⟩

@[simp]
theorem realCl04ToQuaternionMatrix_ι (v : (((ℝ × ℝ) × ℝ) × ℝ)) :
    realCl04ToQuaternionMatrix (CliffordAlgebra.ι realCl04Form v) =
      !![⟨0, v.1.1.1, v.1.1.2, v.1.2⟩, (v.2 : H);
        -(v.2 : H), ⟨0, -v.1.1.1, -v.1.1.2, -v.1.2⟩] := by
  simpa [realCl04ToQuaternionMatrix, realCl04ToQuaternionMatrixLin] using
    (CliffordAlgebra.lift_ι_apply realCl04ToQuaternionMatrixLin
      realCl04ToQuaternionMatrixLin_sq v)

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 4000000 in
theorem realCl04ToQuaternionMatrix_surjective :
    Function.Surjective realCl04ToQuaternionMatrix := by
  intro A
  let e1 : CliffordAlgebra realCl04Form :=
    CliffordAlgebra.ι realCl04Form ((((1 : ℝ), 0), 0), 0)
  let e2 : CliffordAlgebra realCl04Form :=
    CliffordAlgebra.ι realCl04Form ((((0 : ℝ), 1), 0), 0)
  let e3 : CliffordAlgebra realCl04Form :=
    CliffordAlgebra.ι realCl04Form ((((0 : ℝ), 0), 1), 0)
  let e4 : CliffordAlgebra realCl04Form :=
    CliffordAlgebra.ι realCl04Form ((((0 : ℝ), 0), 0), 1)
  refine ⟨((((A 0 0).re + (A 1 1).re) / 2) • (1 : CliffordAlgebra realCl04Form)) +
      ((((A 0 0).imI - (A 1 1).imI) / 2) • e1) +
      ((((A 0 0).imJ - (A 1 1).imJ) / 2) • e2) +
      ((((A 0 0).imK - (A 1 1).imK) / 2) • e3) +
      ((((A 0 1).re - (A 1 0).re) / 2) • e4) +
      ((((A 0 0).imK + (A 1 1).imK) / 2) • (e1 * e2)) +
      ((-((A 0 0).imJ + (A 1 1).imJ) / 2) • (e1 * e3)) +
      ((((A 0 1).imI + (A 1 0).imI) / 2) • (e1 * e4)) +
      ((((A 0 0).imI + (A 1 1).imI) / 2) • (e2 * e3)) +
      ((((A 0 1).imJ + (A 1 0).imJ) / 2) • (e2 * e4)) +
      ((((A 0 1).imK + (A 1 0).imK) / 2) • (e3 * e4)) +
      ((((A 1 1).re - (A 0 0).re) / 2) • (e1 * e2 * e3)) +
      ((((A 0 1).imK - (A 1 0).imK) / 2) • (e1 * e2 * e4)) +
      ((((A 1 0).imJ - (A 0 1).imJ) / 2) • (e1 * e3 * e4)) +
      ((((A 0 1).imI - (A 1 0).imI) / 2) • (e2 * e3 * e4)) +
      ((-((A 0 1).re + (A 1 0).re) / 2) • (e1 * e2 * e3 * e4)), ?_⟩
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [e1, e2, e3, e4, QuaternionAlgebra.mk_mul_mk] <;>
    ring_nf

theorem realCl04Clifford_finrank :
    Module.finrank ℝ (CliffordAlgebra realCl04Form) = 16 := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  let b3raw : Module.Basis (Fin 2 ⊕ Unit) ℝ ((ℝ × ℝ) × ℝ) :=
    (Module.Basis.finTwoProd ℝ).prod (Module.Basis.singleton Unit ℝ)
  let b : Module.Basis ((Fin 2 ⊕ Unit) ⊕ Unit) ℝ ((((ℝ × ℝ) × ℝ) × ℝ)) :=
    b3raw.prod (Module.Basis.singleton Unit ℝ)
  let e3 : Fin 2 ⊕ Unit ≃ Fin 3 :=
    (Equiv.sumCongr (Equiv.refl (Fin 2)) finOneEquiv.symm).trans finSumFinEquiv
  let e4 : (Fin 2 ⊕ Unit) ⊕ Unit ≃ Fin 4 :=
    (Equiv.sumCongr e3 finOneEquiv.symm).trans finSumFinEquiv
  let b4 : Module.Basis (Fin 4) ℝ ((((ℝ × ℝ) × ℝ) × ℝ)) := b.reindex e4
  calc
    Module.finrank ℝ (CliffordAlgebra realCl04Form) =
        Module.finrank ℝ (ExteriorAlgebra ℝ ((((ℝ × ℝ) × ℝ) × ℝ))) := by
      exact LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior realCl04Form)
    _ = Fintype.card (Finset (Fin 4)) := by
      exact Module.finrank_eq_card_basis b4.ExteriorAlgebra
    _ = 16 := by
      simp

theorem realCl04QuaternionMatrix_finrank :
    Module.finrank ℝ (Matrix (Fin 2) (Fin 2) H) = 16 := by
  rw [Module.finrank_matrix]
  rw [QuaternionAlgebra.finrank_eq_four (-1 : ℝ) 0 (-1 : ℝ)]
  norm_num

theorem realCl04ToQuaternionMatrix_injective : Function.Injective realCl04ToQuaternionMatrix := by
  have hcl_succ : Module.finrank ℝ (CliffordAlgebra realCl04Form) = Nat.succ 15 := by
    simpa using realCl04Clifford_finrank
  letI : FiniteDimensional ℝ (CliffordAlgebra realCl04Form) :=
    FiniteDimensional.of_finrank_eq_succ hcl_succ
  have hdim : Module.finrank ℝ (CliffordAlgebra realCl04Form) =
      Module.finrank ℝ (Matrix (Fin 2) (Fin 2) H) := by
    rw [realCl04Clifford_finrank, realCl04QuaternionMatrix_finrank]
  simpa using
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := realCl04ToQuaternionMatrix.toLinearMap) hdim).mpr
      realCl04ToQuaternionMatrix_surjective)

/-- The real Clifford algebra `Cl(0,4)` is the full `2 × 2` quaternionic matrix algebra. -/
noncomputable def realCl04EquivQuaternionMatrix2 :
    CliffordAlgebra realCl04Form ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) H :=
  AlgEquiv.ofBijective realCl04ToQuaternionMatrix
    ⟨realCl04ToQuaternionMatrix_injective, realCl04ToQuaternionMatrix_surjective⟩

@[simp]
theorem realCl04EquivQuaternionMatrix2_apply_ι (v : (((ℝ × ℝ) × ℝ) × ℝ)) :
    realCl04EquivQuaternionMatrix2 (CliffordAlgebra.ι realCl04Form v) =
      !![⟨0, v.1.1.1, v.1.1.2, v.1.2⟩, (v.2 : H);
        -(v.2 : H), ⟨0, -v.1.1.1, -v.1.1.2, -v.1.2⟩] := by
  simp [realCl04EquivQuaternionMatrix2]

/-- The standard positive real 4-dimensional quadratic form on `(((ℝ × ℝ) × ℝ) × ℝ)`. -/
noncomputable abbrev realCl40Form : QuadraticForm ℝ (((ℝ × ℝ) × ℝ) × ℝ) :=
  -realCl04Form

@[simp] theorem realCl40Form_apply (a b c d : ℝ) :
    realCl40Form (((a, b), c), d) = a * a + b * b + c * c + d * d := by
  simp [realCl40Form, realCl04Form]
  ring

/-- The even real Clifford algebra `Cl⁺(4,0)` is isomorphic to `ℍ × ℍ`. -/
noncomputable def realEvenCl40EquivQuaternionProd :
    CliffordAlgebra.even realCl40Form ≃ₐ[ℝ] H × H := by
  simpa [realCl40Form] using
    ((CliffordAlgebra.evenEquivEvenNeg (Q := realCl04Form)).symm.trans
      realEvenCl04EquivQuaternionProd)

set_option linter.unnecessarySeqFocus false in
/-- The generator map for the explicit `Cl(4,0) ≃ Mat₂(ℍ)` model. -/
def realCl40ToQuaternionMatrixLin :
    (((ℝ × ℝ) × ℝ) × ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) H where
  toFun v := !![(v.2 : H), ⟨v.1.1.1, v.1.1.2, v.1.2, 0⟩;
      ⟨v.1.1.1, -v.1.1.2, -v.1.2, 0⟩, -(v.2 : H)]
  map_add' x y := by
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := x
    obtain ⟨⟨⟨e, f⟩, g⟩, h⟩ := y
    ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' a x := by
    obtain ⟨⟨⟨b, c⟩, d⟩, e⟩ := x
    ext i j <;> fin_cases i <;> fin_cases j <;> simp

set_option linter.unnecessarySeqFocus false in
theorem realCl40ToQuaternionMatrixLin_sq (v : (((ℝ × ℝ) × ℝ) × ℝ)) :
    realCl40ToQuaternionMatrixLin v * realCl40ToQuaternionMatrixLin v =
      algebraMap ℝ (Matrix (Fin 2) (Fin 2) H) (realCl40Form v) := by
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := v
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [realCl40ToQuaternionMatrixLin, Matrix.mul_apply, Matrix.algebraMap_matrix_apply,
      QuaternionAlgebra.mk_mul_mk] <;>
    ring_nf

/-- The explicit quaternionic matrix representation of the real Clifford algebra `Cl(4,0)`. -/
noncomputable def realCl40ToQuaternionMatrix :
    CliffordAlgebra realCl40Form →ₐ[ℝ] Matrix (Fin 2) (Fin 2) H :=
  CliffordAlgebra.lift realCl40Form ⟨realCl40ToQuaternionMatrixLin,
    realCl40ToQuaternionMatrixLin_sq⟩

@[simp]
theorem realCl40ToQuaternionMatrix_ι (v : (((ℝ × ℝ) × ℝ) × ℝ)) :
    realCl40ToQuaternionMatrix (CliffordAlgebra.ι realCl40Form v) =
      !![(v.2 : H), ⟨v.1.1.1, v.1.1.2, v.1.2, 0⟩;
        ⟨v.1.1.1, -v.1.1.2, -v.1.2, 0⟩, -(v.2 : H)] := by
  simpa [realCl40ToQuaternionMatrix, realCl40ToQuaternionMatrixLin] using
    (CliffordAlgebra.lift_ι_apply realCl40ToQuaternionMatrixLin
      realCl40ToQuaternionMatrixLin_sq v)

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 4000000 in
theorem realCl40ToQuaternionMatrix_surjective :
    Function.Surjective realCl40ToQuaternionMatrix := by
  intro A
  let e1 : CliffordAlgebra realCl40Form :=
    CliffordAlgebra.ι realCl40Form ((((1 : ℝ), 0), 0), 0)
  let e2 : CliffordAlgebra realCl40Form :=
    CliffordAlgebra.ι realCl40Form ((((0 : ℝ), 1), 0), 0)
  let e3 : CliffordAlgebra realCl40Form :=
    CliffordAlgebra.ι realCl40Form ((((0 : ℝ), 0), 1), 0)
  let e4 : CliffordAlgebra realCl40Form :=
    CliffordAlgebra.ι realCl40Form ((((0 : ℝ), 0), 0), 1)
  refine ⟨((((A 0 0).re + (A 1 1).re) / 2) • (1 : CliffordAlgebra realCl40Form)) +
      ((((A 0 1).re + (A 1 0).re) / 2) • e1) +
      ((((A 0 1).imI - (A 1 0).imI) / 2) • e2) +
      ((((A 0 1).imJ - (A 1 0).imJ) / 2) • e3) +
      ((((A 0 0).re - (A 1 1).re) / 2) • e4) +
      ((((A 1 1).imI - (A 0 0).imI) / 2) • (e1 * e2)) +
      ((((A 1 1).imJ - (A 0 0).imJ) / 2) • (e1 * e3)) +
      ((((A 1 0).re - (A 0 1).re) / 2) • (e1 * e4)) +
      ((-((A 0 0).imK + (A 1 1).imK) / 2) • (e2 * e3)) +
      ((-((A 0 1).imI + (A 1 0).imI) / 2) • (e2 * e4)) +
      ((-((A 0 1).imJ + (A 1 0).imJ) / 2) • (e3 * e4)) +
      ((-((A 0 1).imK + (A 1 0).imK) / 2) • (e1 * e2 * e3)) +
      ((-((A 0 0).imI + (A 1 1).imI) / 2) • (e1 * e2 * e4)) +
      ((-((A 0 0).imJ + (A 1 1).imJ) / 2) • (e1 * e3 * e4)) +
      ((((A 1 1).imK - (A 0 0).imK) / 2) • (e2 * e3 * e4)) +
      ((((A 0 1).imK - (A 1 0).imK) / 2) • (e1 * e2 * e3 * e4)), ?_⟩
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [e1, e2, e3, e4, QuaternionAlgebra.mk_mul_mk] <;>
    ring_nf

theorem realCl40Clifford_finrank :
    Module.finrank ℝ (CliffordAlgebra realCl40Form) = 16 := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  let b3raw : Module.Basis (Fin 2 ⊕ Unit) ℝ ((ℝ × ℝ) × ℝ) :=
    (Module.Basis.finTwoProd ℝ).prod (Module.Basis.singleton Unit ℝ)
  let b : Module.Basis ((Fin 2 ⊕ Unit) ⊕ Unit) ℝ ((((ℝ × ℝ) × ℝ) × ℝ)) :=
    b3raw.prod (Module.Basis.singleton Unit ℝ)
  let e3 : Fin 2 ⊕ Unit ≃ Fin 3 :=
    (Equiv.sumCongr (Equiv.refl (Fin 2)) finOneEquiv.symm).trans finSumFinEquiv
  let e4 : (Fin 2 ⊕ Unit) ⊕ Unit ≃ Fin 4 :=
    (Equiv.sumCongr e3 finOneEquiv.symm).trans finSumFinEquiv
  let b4 : Module.Basis (Fin 4) ℝ ((((ℝ × ℝ) × ℝ) × ℝ)) := b.reindex e4
  calc
    Module.finrank ℝ (CliffordAlgebra realCl40Form) =
        Module.finrank ℝ (ExteriorAlgebra ℝ ((((ℝ × ℝ) × ℝ) × ℝ))) := by
      exact LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior realCl40Form)
    _ = Fintype.card (Finset (Fin 4)) := by
      exact Module.finrank_eq_card_basis b4.ExteriorAlgebra
    _ = 16 := by
      simp

theorem realCl40QuaternionMatrix_finrank :
    Module.finrank ℝ (Matrix (Fin 2) (Fin 2) H) = 16 := by
  rw [Module.finrank_matrix]
  rw [QuaternionAlgebra.finrank_eq_four (-1 : ℝ) 0 (-1 : ℝ)]
  norm_num

theorem realCl40ToQuaternionMatrix_injective : Function.Injective realCl40ToQuaternionMatrix := by
  have hcl_succ : Module.finrank ℝ (CliffordAlgebra realCl40Form) = Nat.succ 15 := by
    simpa using realCl40Clifford_finrank
  letI : FiniteDimensional ℝ (CliffordAlgebra realCl40Form) :=
    FiniteDimensional.of_finrank_eq_succ hcl_succ
  have hdim : Module.finrank ℝ (CliffordAlgebra realCl40Form) =
      Module.finrank ℝ (Matrix (Fin 2) (Fin 2) H) := by
    rw [realCl40Clifford_finrank, realCl40QuaternionMatrix_finrank]
  simpa using
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := realCl40ToQuaternionMatrix.toLinearMap) hdim).mpr
      realCl40ToQuaternionMatrix_surjective)

/-- The real Clifford algebra `Cl(4,0)` is the full `2 × 2` quaternionic matrix algebra. -/
noncomputable def realCl40EquivQuaternionMatrix2 :
    CliffordAlgebra realCl40Form ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) H :=
  AlgEquiv.ofBijective realCl40ToQuaternionMatrix
    ⟨realCl40ToQuaternionMatrix_injective, realCl40ToQuaternionMatrix_surjective⟩

@[simp]
theorem realCl40EquivQuaternionMatrix2_apply_ι (v : (((ℝ × ℝ) × ℝ) × ℝ)) :
    realCl40EquivQuaternionMatrix2 (CliffordAlgebra.ι realCl40Form v) =
      !![(v.2 : H), ⟨v.1.1.1, v.1.1.2, v.1.2, 0⟩;
        ⟨v.1.1.1, -v.1.1.2, -v.1.2, 0⟩, -(v.2 : H)] := by
  simp [realCl40EquivQuaternionMatrix2]

/-- The standard negative real 5-dimensional quadratic form on
`((((ℝ × ℝ) × ℝ) × ℝ) × ℝ)`. -/
noncomputable abbrev realCl05Form : QuadraticForm ℝ ((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) :=
  CliffordAlgebra.EquivEven.Q' realCl04Form

@[simp] theorem realCl05Form_apply (a b c d e : ℝ) :
    realCl05Form ((((a, b), c), d), e) =
      -(a * a + b * b + c * c + d * d + e * e) := by
  simp [realCl05Form, realCl04Form]
  ring

/-- The even real Clifford algebra `Cl⁺(0,5)` is isomorphic to `Mat₂(ℍ)`. -/
noncomputable def realEvenCl05EquivQuaternionMatrix2 :
    CliffordAlgebra.even realCl05Form ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) H := by
  simpa [realCl05Form] using
    ((CliffordAlgebra.equivEven realCl04Form).symm.trans realCl04EquivQuaternionMatrix2)

/-- The standard positive real 5-dimensional quadratic form on
`((((ℝ × ℝ) × ℝ) × ℝ) × ℝ)`. -/
noncomputable abbrev realCl50Form : QuadraticForm ℝ ((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) :=
  -realCl05Form

@[simp] theorem realCl50Form_apply (a b c d e : ℝ) :
    realCl50Form ((((a, b), c), d), e) = a * a + b * b + c * c + d * d + e * e := by
  simp [realCl50Form, realCl05Form]
  ring

/-- The even real Clifford algebra `Cl⁺(5,0)` is isomorphic to `Mat₂(ℍ)`. -/
noncomputable def realEvenCl50EquivQuaternionMatrix2 :
    CliffordAlgebra.even realCl50Form ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) H := by
  simpa [realCl50Form] using
    ((CliffordAlgebra.evenEquivEvenNeg (Q := realCl05Form)).symm.trans
      realEvenCl05EquivQuaternionMatrix2)

namespace RealClassification

/-- Canonical quadratic form for `Cl(0,3)` in the real-classification namespace. -/
noncomputable abbrev Q_0_3 : QuadraticForm ℝ ((ℝ × ℝ) × ℝ) :=
  realCl03Form

/-- Canonical real-classification entry: `Cl(0,3) ≃ ℍ × ℍ`. -/
noncomputable def cl_0_3_equivQuaternionProd :
    CliffordAlgebra Q_0_3 ≃ₐ[ℝ] H × H := by
  simpa [Q_0_3] using Cl03QuaternionProd.realCl03EquivQuaternionProd

/-- Canonical even real-classification entry: `Cl⁺(0,3) ≃ ℍ`. -/
noncomputable def cl_0_3_even_equivQuaternion :
    CliffordAlgebra.even Q_0_3 ≃ₐ[ℝ] H := by
  simpa [Q_0_3] using realEvenCl03EquivQuaternion

/-- Canonical quadratic form for the even algebra `Cl⁺(0,4)` in the real-classification
namespace. -/
noncomputable abbrev Q_0_4 : QuadraticForm ℝ (((ℝ × ℝ) × ℝ) × ℝ) :=
  realCl04Form

/-- Canonical real-classification entry: `Cl⁺(0,4) ≃ ℍ × ℍ`. -/
noncomputable def cl_0_4_even_equivQuaternionProd :
    CliffordAlgebra.even Q_0_4 ≃ₐ[ℝ] H × H := by
  simpa [Q_0_4] using realEvenCl04EquivQuaternionProd

/-- Canonical real-classification entry: `Cl(0,4) ≃ Mat₂(ℍ)`. -/
noncomputable def cl_0_4_equivQuaternionMatrix2 :
    CliffordAlgebra Q_0_4 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) H := by
  simpa [Q_0_4] using realCl04EquivQuaternionMatrix2

/-- Canonical quadratic form for `Cl(0,5)` and its even algebra in the real-classification
namespace. -/
noncomputable abbrev Q_0_5 : QuadraticForm ℝ ((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) :=
  realCl05Form

/-- Canonical even real-classification entry: `Cl⁺(0,5) ≃ Mat₂(ℍ)`. -/
noncomputable def cl_0_5_even_equivQuaternionMatrix2 :
    CliffordAlgebra.even Q_0_5 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) H := by
  simpa [Q_0_5] using realEvenCl05EquivQuaternionMatrix2

/-- Canonical quadratic form for `Cl(4,0)` and its even algebra in the real-classification
namespace. -/
noncomputable abbrev Q_4_0 : QuadraticForm ℝ (((ℝ × ℝ) × ℝ) × ℝ) :=
  realCl40Form

/-- Canonical even real-classification entry: `Cl⁺(4,0) ≃ ℍ × ℍ`. -/
noncomputable def cl_4_0_even_equivQuaternionProd :
    CliffordAlgebra.even Q_4_0 ≃ₐ[ℝ] H × H := by
  simpa [Q_4_0] using realEvenCl40EquivQuaternionProd

/-- Canonical real-classification entry: `Cl(4,0) ≃ Mat₂(ℍ)`. -/
noncomputable def cl_4_0_equivQuaternionMatrix2 :
    CliffordAlgebra Q_4_0 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) H := by
  simpa [Q_4_0] using realCl40EquivQuaternionMatrix2

/-- Canonical quadratic form for `Cl(5,0)` and its even algebra in the real-classification
namespace. -/
noncomputable abbrev Q_5_0 : QuadraticForm ℝ ((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) :=
  realCl50Form

/-- Canonical even real-classification entry: `Cl⁺(5,0) ≃ Mat₂(ℍ)`. -/
noncomputable def cl_5_0_even_equivQuaternionMatrix2 :
    CliffordAlgebra.even Q_5_0 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) H := by
  simpa [Q_5_0] using realEvenCl50EquivQuaternionMatrix2

end RealClassification

@[simp] theorem realEvenCl04EquivQuaternionProd_apply_star (x : CliffordAlgebra.even realCl04Form) :
    realEvenCl04EquivQuaternionProd
        ⟨star (x : CliffordAlgebra realCl04Form), by
          simp [CliffordAlgebra.even, CliffordAlgebra.star_def,
            CliffordAlgebra.reverse_mem_evenOdd_iff, CliffordAlgebra.involute_mem_evenOdd_iff]⟩ =
      star (realEvenCl04EquivQuaternionProd x) := by
  change Cl03QuaternionProd.realCl03EquivQuaternionProd
      ((CliffordAlgebra.equivEven realCl03Form).symm
        ⟨star (x : CliffordAlgebra realCl04Form), by
          simp [CliffordAlgebra.even, CliffordAlgebra.star_def,
            CliffordAlgebra.reverse_mem_evenOdd_iff, CliffordAlgebra.involute_mem_evenOdd_iff]⟩) =
      star (Cl03QuaternionProd.realCl03EquivQuaternionProd ((CliffordAlgebra.equivEven realCl03Form).symm x))
  rw [cliffordEquivEven_symm_apply_star, Cl03QuaternionProd.realCl03EquivQuaternionProd_apply_star]

@[simp] theorem realEvenCl04EquivQuaternionProd_apply_bilin
    (x y : (((ℝ × ℝ) × ℝ) × ℝ)) :
    realEvenCl04EquivQuaternionProd ((CliffordAlgebra.even.ι realCl04Form).bilin x y) =
      (((⟨x.2, x.1.1.1, x.1.1.2, x.1.2⟩ : H) *
          ⟨-y.2, y.1.1.1, y.1.1.2, y.1.2⟩),
        ((⟨x.2, x.1.1.1, x.1.1.2, -x.1.2⟩ : H) *
          ⟨-y.2, y.1.1.1, y.1.1.2, -y.1.2⟩)) := by
  obtain ⟨⟨⟨x1, x2⟩, x3⟩, x4⟩ := x
  obtain ⟨⟨⟨y1, y2⟩, y3⟩, y4⟩ := y
  change
    Cl03QuaternionProd.toQuatPair
        ((CliffordAlgebra.equivEven realCl03Form).symm
          ((CliffordAlgebra.even.ι realCl04Form).bilin (((x1, x2), x3), x4) (((y1, y2), y3), y4))) =
      _
  rw [show
      (CliffordAlgebra.equivEven realCl03Form).symm
          ((CliffordAlgebra.even.ι realCl04Form).bilin (((x1, x2), x3), x4) (((y1, y2), y3), y4)) =
        CliffordAlgebra.ofEven realCl03Form
          ((CliffordAlgebra.even.ι realCl04Form).bilin (((x1, x2), x3), x4) (((y1, y2), y3), y4)) by
      rfl]
  rw [CliffordAlgebra.ofEven_ι]
  rw [map_mul, map_add, map_sub]
  ext <;> simp [Cl03QuaternionProd.toQuatPair, Cl03QuaternionProd.toH_ι,
    QuaternionAlgebra.mk_mul_mk]

@[simp] theorem realCl04Form_apply (a b c d : ℝ) :
    realCl04Form (((a, b), c), d) = -(a * a + b * b + c * c + d * d) := by
  simp [realCl04Form]
  ring

/-- Embed a slice quaternion `a + bi + cj` as a left unit vector in `ℝ⁴`,
with the third spatial coordinate fixed to zero. -/
abbrev quaternionDiagLeftVector (q : H) : (((ℝ × ℝ) × ℝ) × ℝ) :=
  (((q.imI, q.imJ), 0), q.re)

/-- Embed a slice quaternion `a + bi + cj` as a right unit vector in `ℝ⁴`,
with the third spatial coordinate fixed to zero. -/
abbrev quaternionDiagRightVector (q : H) : (((ℝ × ℝ) × ℝ) × ℝ) :=
  (((q.imI, q.imJ), 0), -q.re)

theorem realCl04Form_diagLeftVector_eq_neg_one
    (q : unitary H) (hk : (q : H).imK = 0) :
    realCl04Form (quaternionDiagLeftVector (q : H)) = -1 := by
  rw [realCl04Form_apply]
  have hq := unitaryQuaternion_sqSum_eq_one q
  nlinarith [hq, hk]

theorem realCl04Form_diagRightVector_eq_neg_one
    (q : unitary H) (hk : (q : H).imK = 0) :
    realCl04Form (quaternionDiagRightVector (q : H)) = -1 := by
  rw [realCl04Form_apply]
  have hq := unitaryQuaternion_sqSum_eq_one q
  nlinarith [hq, hk]

/-- The `k`-axis copy of `U(1)` inside the unit quaternions. -/
noncomputable def unitaryComplexToUnitaryQuaternionK (z : unitary ℂ) : unitary H := by
  refine ⟨⟨(z : ℂ).re, 0, 0, (z : ℂ).im⟩, ?_⟩
  rw [Unitary.mem_iff]
  have hz_complex : ((Complex.normSq (z : ℂ) : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    simpa [Complex.star_def] using
      (Unitary.coe_star_mul_self z : ((star z : unitary ℂ) : ℂ) * z = 1)
  have hz_norm : Complex.normSq (z : ℂ) = 1 :=
    Complex.ofReal_injective hz_complex
  have hmul : (z : ℂ).re * (z : ℂ).re + (z : ℂ).im * (z : ℂ).im = 1 := by
    simpa [Complex.normSq_apply] using hz_norm
  constructor
  · ext <;> simp
    · exact hmul
    · ring
  · ext <;> simp
    · exact hmul
    · ring

/-- Fixed left vector for the anti-diagonal complex slice inside `Spin(4)`. -/
abbrev complexKLeftBaseVector : (((ℝ × ℝ) × ℝ) × ℝ) :=
  (((0, 0), 0), 1)

/-- Right vector encoding a unit complex number in the `k`-slice. -/
abbrev complexKRightVector (z : ℂ) : (((ℝ × ℝ) × ℝ) × ℝ) :=
  (((0, 0), z.im), -z.re)

@[simp] theorem realCl04Form_complexKLeftBaseVector_eq_neg_one :
    realCl04Form complexKLeftBaseVector = -1 := by
  simp [complexKLeftBaseVector]

theorem realCl04Form_complexKRightVector_eq_neg_one (z : unitary ℂ) :
    realCl04Form (complexKRightVector (z : ℂ)) = -1 := by
  have hz_complex : ((Complex.normSq (z : ℂ) : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    simpa [Complex.star_def] using
      (Unitary.coe_star_mul_self z : ((star z : unitary ℂ) : ℂ) * z = 1)
  have hz_norm : Complex.normSq (z : ℂ) = 1 :=
    Complex.ofReal_injective hz_complex
  rw [realCl04Form_apply]
  rw [Complex.normSq_apply] at hz_norm
  nlinarith

theorem realEvenCl04EquivQuaternionProd_apply_bilin_diag_slice
    (p r : unitary H)
    (hp : (p : H).imK = 0) (hr : (r : H).imK = 0) :
    realEvenCl04EquivQuaternionProd
        ((CliffordAlgebra.even.ι realCl04Form).bilin
          (quaternionDiagLeftVector (p : H))
          (quaternionDiagRightVector (r : H))) =
      (((p : H) * r : H), ((p : H) * r : H)) := by
  ext <;> simp [realEvenCl04EquivQuaternionProd_apply_bilin, quaternionDiagLeftVector,
    quaternionDiagRightVector, hp, hr, QuaternionAlgebra.mk_mul_mk]

noncomputable def realSpin04DiagonalPreimageEven
    (q : unitary H) :
    CliffordAlgebra.even realCl04Form :=
  (CliffordAlgebra.even.ι realCl04Form).bilin
    (quaternionDiagLeftVector
      ((realSpin03LeftSlice q : unitary H) : H))
    (quaternionDiagRightVector
      ((realSpin03RightSlice q : unitary H) : H))

noncomputable def unitaryQuaternionToSpinGroupRealCl04Diagonal
    (q : unitary H) :
    spinGroup realCl04Form := by
  have hLeft : realCl04Form
      (quaternionDiagLeftVector
        ((realSpin03LeftSlice q : unitary H) : H)) = -1 :=
    realCl04Form_diagLeftVector_eq_neg_one
      (realSpin03LeftSlice q) (realSpin03LeftSlice_imK q)
  have hRight : realCl04Form
      (quaternionDiagRightVector
        ((realSpin03RightSlice q : unitary H) : H)) = -1 :=
    realCl04Form_diagRightVector_eq_neg_one
      (realSpin03RightSlice q) (realSpin03RightSlice_imK q)
  refine ⟨realSpin04DiagonalPreimageEven q, ?_⟩
  refine ⟨?_, (realSpin04DiagonalPreimageEven q).property⟩
  change
    (CliffordAlgebra.ι realCl04Form
        (quaternionDiagLeftVector
          ((realSpin03LeftSlice q : unitary H) : H)) *
      CliffordAlgebra.ι realCl04Form
        (quaternionDiagRightVector
          ((realSpin03RightSlice q : unitary H) : H))) ∈
      pinGroup realCl04Form
  exact Submonoid.mul_mem _
    (iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := realCl04Form)
      (quaternionDiagLeftVector
        ((realSpin03LeftSlice q : unitary H) : H)) hLeft)
    (iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := realCl04Form)
      (quaternionDiagRightVector
        ((realSpin03RightSlice q : unitary H) : H)) hRight)

noncomputable def realSpin04AntidiagonalComplexPreimageEven
    (z : unitary ℂ) :
    CliffordAlgebra.even realCl04Form :=
  (CliffordAlgebra.even.ι realCl04Form).bilin
    complexKLeftBaseVector
    (complexKRightVector (z : ℂ))

noncomputable def unitaryComplexToSpinGroupRealCl04Antidiagonal
    (z : unitary ℂ) :
    spinGroup realCl04Form := by
  have hLeft : realCl04Form complexKLeftBaseVector = -1 :=
    realCl04Form_complexKLeftBaseVector_eq_neg_one
  have hRight : realCl04Form (complexKRightVector (z : ℂ)) = -1 :=
    realCl04Form_complexKRightVector_eq_neg_one z
  refine ⟨realSpin04AntidiagonalComplexPreimageEven z, ?_⟩
  refine ⟨?_, (realSpin04AntidiagonalComplexPreimageEven z).property⟩
  change
    (CliffordAlgebra.ι realCl04Form complexKLeftBaseVector *
      CliffordAlgebra.ι realCl04Form (complexKRightVector (z : ℂ))) ∈
      pinGroup realCl04Form
  exact Submonoid.mul_mem _
    (iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := realCl04Form)
      complexKLeftBaseVector hLeft)
    (iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := realCl04Form)
      (complexKRightVector (z : ℂ)) hRight)

noncomputable def spinGroupRealCl04ToQuaternionProd :
    spinGroup realCl04Form →* (H × H) :=
  realEvenCl04EquivQuaternionProd.toMonoidHom.comp (spinGroupToEven realCl04Form)

theorem spinGroupRealCl04ToQuaternionProd_mem_unitary (x : spinGroup realCl04Form) :
    spinGroupRealCl04ToQuaternionProd x ∈ unitary (H × H) := by
  rw [Unitary.mem_iff]
  let x₀ : CliffordAlgebra.even realCl04Form := spinGroupToEven realCl04Form x
  let xStar : CliffordAlgebra.even realCl04Form := ⟨star (x : CliffordAlgebra realCl04Form), by
    simpa [CliffordAlgebra.even, CliffordAlgebra.even_toSubmodule, CliffordAlgebra.star_def,
      CliffordAlgebra.reverse_mem_evenOdd_iff, CliffordAlgebra.involute_mem_evenOdd_iff] using
      (spinGroup.mem_even x.prop)⟩
  constructor
  · change star (realEvenCl04EquivQuaternionProd x₀) * realEvenCl04EquivQuaternionProd x₀ = 1
    rw [← realEvenCl04EquivQuaternionProd_apply_star, ← map_mul]
    have hx : xStar * x₀ = 1 := by
      ext
      exact spinGroup.coe_star_mul_self x
    change realEvenCl04EquivQuaternionProd (xStar * x₀) = 1
    rw [hx, map_one]
  · change realEvenCl04EquivQuaternionProd x₀ * star (realEvenCl04EquivQuaternionProd x₀) = 1
    rw [← realEvenCl04EquivQuaternionProd_apply_star, ← map_mul]
    have hx : x₀ * xStar = 1 := by
      ext
      exact spinGroup.coe_mul_star_self x
    change realEvenCl04EquivQuaternionProd (x₀ * xStar) = 1
    rw [hx, map_one]

noncomputable def spinGroupRealCl04ToUnitaryQuaternionProd :
    spinGroup realCl04Form →* unitary (H × H) :=
  (spinGroupRealCl04ToQuaternionProd).codRestrict
    (unitary (H × H))
    spinGroupRealCl04ToQuaternionProd_mem_unitary

noncomputable def unitaryQuaternionProdEquiv :
    unitary (H × H) ≃* unitary H × unitary H where
  toFun u := by
    refine ⟨?_, ?_⟩
    · refine ⟨u.1.1, ?_⟩
      rw [Unitary.mem_iff]
      exact ⟨congrArg Prod.fst u.property.1, congrArg Prod.fst u.property.2⟩
    · refine ⟨u.1.2, ?_⟩
      rw [Unitary.mem_iff]
      exact ⟨congrArg Prod.snd u.property.1, congrArg Prod.snd u.property.2⟩
  invFun u := by
    refine ⟨(u.1, u.2), ?_⟩
    rw [Unitary.mem_iff]
    constructor <;> ext <;> simp
  left_inv u := by
    ext <;> rfl
  right_inv u := by
    ext <;> rfl
  map_mul' u v := rfl

noncomputable def spinGroupRealCl04ToUnitaryQuaternionPair :
    spinGroup realCl04Form →* (unitary H × unitary H) :=
  unitaryQuaternionProdEquiv.toMonoidHom.comp spinGroupRealCl04ToUnitaryQuaternionProd

@[simp] theorem spinGroupRealCl04ToQuaternionProd_apply_diag_preimage
    (q : unitary H) :
    spinGroupRealCl04ToQuaternionProd
        (unitaryQuaternionToSpinGroupRealCl04Diagonal q) =
      ((q : H), (q : H)) := by
  change
    realEvenCl04EquivQuaternionProd
      (spinGroupToEven realCl04Form
        (unitaryQuaternionToSpinGroupRealCl04Diagonal q)) =
      ((q : H), (q : H))
  have hEven :
      spinGroupToEven realCl04Form
        (unitaryQuaternionToSpinGroupRealCl04Diagonal q) =
      realSpin04DiagonalPreimageEven q := by
    apply Subtype.ext
    simp [spinGroupToEven, unitaryQuaternionToSpinGroupRealCl04Diagonal,
      realSpin04DiagonalPreimageEven]
  rw [hEven, realSpin04DiagonalPreimageEven,
    realEvenCl04EquivQuaternionProd_apply_bilin_diag_slice
      (realSpin03LeftSlice q) (realSpin03RightSlice q)
      (realSpin03LeftSlice_imK q) (realSpin03RightSlice_imK q)]
  simpa using congrArg (fun z : H => (z, z)) (realSpin03LeftSlice_mul_rightSlice q)

@[simp] theorem spinGroupRealCl04ToQuaternionProd_apply_antidiag_complex_preimage
    (z : unitary ℂ) :
    spinGroupRealCl04ToQuaternionProd
        (unitaryComplexToSpinGroupRealCl04Antidiagonal z) =
      (((unitaryComplexToUnitaryQuaternionK z : unitary H) : H),
        (star (unitaryComplexToUnitaryQuaternionK z) : H)) := by
  change
    realEvenCl04EquivQuaternionProd
      (spinGroupToEven realCl04Form
        (unitaryComplexToSpinGroupRealCl04Antidiagonal z)) =
      (((unitaryComplexToUnitaryQuaternionK z : unitary H) : H),
        (star (unitaryComplexToUnitaryQuaternionK z) : H))
  have hEven :
      spinGroupToEven realCl04Form
        (unitaryComplexToSpinGroupRealCl04Antidiagonal z) =
      realSpin04AntidiagonalComplexPreimageEven z := by
    apply Subtype.ext
    simp [spinGroupToEven, unitaryComplexToSpinGroupRealCl04Antidiagonal,
      realSpin04AntidiagonalComplexPreimageEven]
  rw [hEven, realSpin04AntidiagonalComplexPreimageEven,
    realEvenCl04EquivQuaternionProd_apply_bilin]
  ext <;> simp [unitaryComplexToUnitaryQuaternionK, QuaternionAlgebra.mk_mul_mk]

@[simp] theorem spinGroupRealCl04ToUnitaryQuaternionProd_apply_diag_preimage
    (q : unitary H) :
    spinGroupRealCl04ToUnitaryQuaternionProd
        (unitaryQuaternionToSpinGroupRealCl04Diagonal q) =
      ⟨((q : H), (q : H)), by
        rw [Unitary.mem_iff]
        constructor <;> ext <;> simp⟩ := by
  apply Subtype.ext
  exact spinGroupRealCl04ToQuaternionProd_apply_diag_preimage q

@[simp] theorem spinGroupRealCl04ToUnitaryQuaternionPair_apply_diag_preimage
    (q : unitary H) :
    spinGroupRealCl04ToUnitaryQuaternionPair
        (unitaryQuaternionToSpinGroupRealCl04Diagonal q) =
      (q, q) := by
  change unitaryQuaternionProdEquiv
      (spinGroupRealCl04ToUnitaryQuaternionProd
        (unitaryQuaternionToSpinGroupRealCl04Diagonal q)) =
    (q, q)
  rw [spinGroupRealCl04ToUnitaryQuaternionProd_apply_diag_preimage]
  ext <;> rfl

@[simp] theorem spinGroupRealCl04ToUnitaryQuaternionPair_apply_antidiag_complex_preimage
    (z : unitary ℂ) :
    spinGroupRealCl04ToUnitaryQuaternionPair
        (unitaryComplexToSpinGroupRealCl04Antidiagonal z) =
      (unitaryComplexToUnitaryQuaternionK z, star (unitaryComplexToUnitaryQuaternionK z)) := by
  change unitaryQuaternionProdEquiv
      (spinGroupRealCl04ToUnitaryQuaternionProd
        (unitaryComplexToSpinGroupRealCl04Antidiagonal z)) =
    (unitaryComplexToUnitaryQuaternionK z, star (unitaryComplexToUnitaryQuaternionK z))
  rw [show
      spinGroupRealCl04ToUnitaryQuaternionProd
          (unitaryComplexToSpinGroupRealCl04Antidiagonal z) =
        ⟨(((unitaryComplexToUnitaryQuaternionK z : unitary H) : H),
            (star (unitaryComplexToUnitaryQuaternionK z) : H)), by
            rw [Unitary.mem_iff]
            constructor <;> ext <;> simp⟩ by
      apply Subtype.ext
      exact spinGroupRealCl04ToQuaternionProd_apply_antidiag_complex_preimage z]
  ext <;> rfl

/-- Fixed left vector for the full anti-diagonal subgroup in `Spin(4)`. -/
abbrev quaternionAntidiagLeftBaseVector : (((ℝ × ℝ) × ℝ) × ℝ) :=
  (((0, 0), 1), 0)

/-- Right vector whose bilinear image is the anti-diagonal pair `(q, star q)`. -/
abbrev quaternionAntidiagRightVector (q : H) : (((ℝ × ℝ) × ℝ) × ℝ) :=
  (((q.imJ, -q.imI), -q.re), -q.imK)

@[simp] theorem realCl04Form_antidiagLeftBaseVector_eq_neg_one :
    realCl04Form quaternionAntidiagLeftBaseVector = -1 := by
  simp [quaternionAntidiagLeftBaseVector]

theorem realCl04Form_antidiagRightVector_eq_neg_one (q : unitary H) :
    realCl04Form (quaternionAntidiagRightVector (q : H)) = -1 := by
  rw [realCl04Form_apply]
  have hq := unitaryQuaternion_sqSum_eq_one q
  nlinarith

noncomputable def realSpin04AntidiagonalPreimageEven
    (q : unitary H) :
    CliffordAlgebra.even realCl04Form :=
  (CliffordAlgebra.even.ι realCl04Form).bilin
    quaternionAntidiagLeftBaseVector
    (quaternionAntidiagRightVector (q : H))

noncomputable def unitaryQuaternionToSpinGroupRealCl04Antidiagonal
    (q : unitary H) :
    spinGroup realCl04Form := by
  have hLeft : realCl04Form quaternionAntidiagLeftBaseVector = -1 :=
    realCl04Form_antidiagLeftBaseVector_eq_neg_one
  have hRight : realCl04Form (quaternionAntidiagRightVector (q : H)) = -1 :=
    realCl04Form_antidiagRightVector_eq_neg_one q
  refine ⟨realSpin04AntidiagonalPreimageEven q, ?_⟩
  refine ⟨?_, (realSpin04AntidiagonalPreimageEven q).property⟩
  change
    (CliffordAlgebra.ι realCl04Form quaternionAntidiagLeftBaseVector *
      CliffordAlgebra.ι realCl04Form (quaternionAntidiagRightVector (q : H))) ∈
      pinGroup realCl04Form
  exact Submonoid.mul_mem _
    (iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := realCl04Form)
      quaternionAntidiagLeftBaseVector hLeft)
    (iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := realCl04Form)
      (quaternionAntidiagRightVector (q : H)) hRight)

@[simp] theorem spinGroupRealCl04ToQuaternionProd_apply_antidiag_preimage
    (q : unitary H) :
    spinGroupRealCl04ToQuaternionProd
        (unitaryQuaternionToSpinGroupRealCl04Antidiagonal q) =
      ((q : H), (star q : H)) := by
  change
    realEvenCl04EquivQuaternionProd
      (spinGroupToEven realCl04Form
        (unitaryQuaternionToSpinGroupRealCl04Antidiagonal q)) =
      ((q : H), (star q : H))
  have hEven :
      spinGroupToEven realCl04Form
        (unitaryQuaternionToSpinGroupRealCl04Antidiagonal q) =
      realSpin04AntidiagonalPreimageEven q := by
    apply Subtype.ext
    simp [spinGroupToEven, unitaryQuaternionToSpinGroupRealCl04Antidiagonal,
      realSpin04AntidiagonalPreimageEven]
  rw [hEven, realSpin04AntidiagonalPreimageEven,
    realEvenCl04EquivQuaternionProd_apply_bilin]
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

@[simp] theorem spinGroupRealCl04ToUnitaryQuaternionPair_apply_antidiag_preimage
    (q : unitary H) :
    spinGroupRealCl04ToUnitaryQuaternionPair
        (unitaryQuaternionToSpinGroupRealCl04Antidiagonal q) =
      (q, star q) := by
  change unitaryQuaternionProdEquiv
      (spinGroupRealCl04ToUnitaryQuaternionProd
        (unitaryQuaternionToSpinGroupRealCl04Antidiagonal q)) =
    (q, star q)
  rw [show
      spinGroupRealCl04ToUnitaryQuaternionProd
          (unitaryQuaternionToSpinGroupRealCl04Antidiagonal q) =
        ⟨(((q : H)), ((star q : unitary H) : H)), by
            rw [Unitary.mem_iff]
            constructor <;> ext <;> simp⟩ by
      apply Subtype.ext
      exact spinGroupRealCl04ToQuaternionProd_apply_antidiag_preimage q]
  ext <;> rfl

theorem unitaryQuaternion_eq_neg_one_of_re_eq_neg_one
    (u : unitary H) (h : (u : H).re = -1) :
    (u : H) = -1 := by
  ext <;> simp [h]
  · have hu := unitaryQuaternion_sqSum_eq_one u
    nlinarith
  · have hu := unitaryQuaternion_sqSum_eq_one u
    nlinarith
  · have hu := unitaryQuaternion_sqSum_eq_one u
    nlinarith

/-- A canonical square root of a unit quaternion, with a fixed `k`-axis choice at `-1`. -/
noncomputable def unitaryQuaternionCanonicalSqrt (u : unitary H) : unitary H := by
  by_cases h : (u : H).re = -1
  · exact ⟨⟨0, 0, 0, 1⟩, by
      rw [Unitary.mem_iff]
      constructor <;> ext <;> simp⟩
  · let a : ℝ := (u : H).re
    let b : ℝ := (u : H).imI
    let c : ℝ := (u : H).imJ
    let d : ℝ := (u : H).imK
    let s : ℝ := Real.sqrt ((a + 1) / 2)
    have hs_sq : s ^ 2 = (a + 1) / 2 := by
      dsimp [s]
      nlinarith [Real.sq_sqrt (show 0 ≤ (a + 1) / 2 by
        have hu := unitaryQuaternion_sqSum_eq_one u
        nlinarith [hu])]
    have hs : s ≠ 0 := by
      intro hs0
      have : (a + 1) / 2 = 0 := by nlinarith [hs_sq, hs0]
      apply h
      nlinarith
    refine ⟨⟨s, b / (2 * s), c / (2 * s), d / (2 * s)⟩, ?_⟩
    rw [Unitary.mem_iff]
    have hu := unitaryQuaternion_sqSum_eq_one u
    constructor <;> ext <;> simp [b, c, d]
    · field_simp [hs]
      ring_nf at *
      nlinarith [hu, hs_sq]
    · ring
    · ring
    · ring
    · field_simp [hs]
      ring_nf at *
      nlinarith [hu, hs_sq]
    · ring
    · ring
    · ring

theorem unitaryQuaternionCanonicalSqrt_sq (u : unitary H) :
    ((unitaryQuaternionCanonicalSqrt u : unitary H) : H) *
        ((unitaryQuaternionCanonicalSqrt u : unitary H) : H) =
      (u : H) := by
  by_cases h : (u : H).re = -1
  · have hu : (u : H) = -1 := unitaryQuaternion_eq_neg_one_of_re_eq_neg_one u h
    have hk :
        ((unitaryQuaternionCanonicalSqrt u : unitary H) : H) = ⟨0, 0, 0, 1⟩ := by
      simp [unitaryQuaternionCanonicalSqrt, h]
    rw [hk, hu]
    ext <;> simp
  · let a : ℝ := (u : H).re
    let b : ℝ := (u : H).imI
    let c : ℝ := (u : H).imJ
    let d : ℝ := (u : H).imK
    let s : ℝ := Real.sqrt ((a + 1) / 2)
    have hs_sq : s ^ 2 = (a + 1) / 2 := by
      dsimp [s]
      nlinarith [Real.sq_sqrt (show 0 ≤ (a + 1) / 2 by
        have hu := unitaryQuaternion_sqSum_eq_one u
        nlinarith [hu])]
    have hs : s ≠ 0 := by
      intro hs0
      have : (a + 1) / 2 = 0 := by nlinarith [hs_sq, hs0]
      apply h
      nlinarith
    have hsqrt :
        ((unitaryQuaternionCanonicalSqrt u : unitary H) : H) =
          ⟨s, b / (2 * s), c / (2 * s), d / (2 * s)⟩ := by
      simp [unitaryQuaternionCanonicalSqrt, h, a, b, c, d, s]
    rw [hsqrt]
    ext <;> simp [QuaternionAlgebra.mk_mul_mk]
    · field_simp [hs]
      have hu := unitaryQuaternion_sqSum_eq_one u
      nlinarith [hu, hs_sq]
    · field_simp [hs]
      ring
    · field_simp [hs]
      ring
    · field_simp [hs]
      ring

noncomputable def unitaryQuaternionPairToSpinGroupRealCl04
    (p r : unitary H) :
    spinGroup realCl04Form :=
  let q₂ : unitary H := unitaryQuaternionCanonicalSqrt (star r * p)
  let q₁ : unitary H := p * star q₂
  unitaryQuaternionToSpinGroupRealCl04Diagonal q₁ *
    unitaryQuaternionToSpinGroupRealCl04Antidiagonal q₂

@[simp] theorem spinGroupRealCl04ToUnitaryQuaternionPair_apply_preimage
    (p r : unitary H) :
    spinGroupRealCl04ToUnitaryQuaternionPair
        (unitaryQuaternionPairToSpinGroupRealCl04 p r) =
      (p, r) := by
  dsimp [unitaryQuaternionPairToSpinGroupRealCl04]
  let q₂ : unitary H := unitaryQuaternionCanonicalSqrt (star r * p)
  let q₁ : unitary H := p * star q₂
  rw [map_mul, spinGroupRealCl04ToUnitaryQuaternionPair_apply_diag_preimage,
    spinGroupRealCl04ToUnitaryQuaternionPair_apply_antidiag_preimage]
  apply Prod.ext <;> apply Subtype.ext
  · change ((q₁ : unitary H) : H) * (q₂ : H) = (p : H)
    dsimp [q₁]
    rw [mul_assoc, Unitary.coe_star_mul_self q₂, mul_one]
  · change ((q₁ : unitary H) : H) * (star q₂ : H) = (r : H)
    dsimp [q₁]
    have hsq : (q₂ : H) * (q₂ : H) = ((star r : unitary H) * p : H) := by
      simpa [q₂] using unitaryQuaternionCanonicalSqrt_sq (star r * p)
    have hsq_star : (star q₂ : H) * (star q₂ : H) = ((star p : unitary H) * r : H) := by
      simpa [q₂, mul_assoc] using congrArg star hsq
    rw [mul_assoc, hsq_star]
    change (p : H) * ((star p : H) * (r : H)) = (r : H)
    rw [← mul_assoc]
    have hpstar : (p : H) * (star p : H) = 1 := by
      exact Unitary.coe_mul_star_self p
    rw [hpstar, one_mul]

theorem spinGroupRealCl04ToUnitaryQuaternionPair_surjective :
    Function.Surjective spinGroupRealCl04ToUnitaryQuaternionPair := by
  rintro ⟨p, r⟩
  exact ⟨unitaryQuaternionPairToSpinGroupRealCl04 p r,
    spinGroupRealCl04ToUnitaryQuaternionPair_apply_preimage p r⟩

theorem spinGroupRealCl04ToUnitaryQuaternionProd_injective :
    Function.Injective spinGroupRealCl04ToUnitaryQuaternionProd := by
  intro x y h
  have h' : spinGroupRealCl04ToQuaternionProd x = spinGroupRealCl04ToQuaternionProd y := congrArg Subtype.val h
  have hEven : spinGroupToEven realCl04Form x = spinGroupToEven realCl04Form y := by
    apply realEvenCl04EquivQuaternionProd.injective
    simpa [spinGroupRealCl04ToQuaternionProd] using h'
  apply Subtype.ext
  simpa [spinGroupToEven] using congrArg Subtype.val hEven

theorem spinGroupRealCl04ToUnitaryQuaternionPair_injective :
    Function.Injective spinGroupRealCl04ToUnitaryQuaternionPair :=
  unitaryQuaternionProdEquiv.injective.comp spinGroupRealCl04ToUnitaryQuaternionProd_injective

noncomputable def realSpin04EquivUnitaryQuaternionPair :
    spinGroup realCl04Form ≃* unitary H × unitary H :=
  MulEquiv.ofBijective spinGroupRealCl04ToUnitaryQuaternionPair
    ⟨spinGroupRealCl04ToUnitaryQuaternionPair_injective,
      spinGroupRealCl04ToUnitaryQuaternionPair_surjective⟩

end Spinor
