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
  simp [realCl03Form, CliffordAlgebra.EquivEven.Q'_apply, realCl02Form_apply]
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
    ext <;> simp <;> ring
  map_smul' r x := by
    cases x with | mk x₁ x₂ =>
    cases x₁ with | mk x₁a x₁b =>
    ext <;> simp <;> ring

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
  ext <;> simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul,
    Algebra.algebraMap_eq_smul_one]

@[simp] lemma toH_one_pPlus : toH 1 (by ring) pPlus = 0 := by
  show toH 1 (by ring) ((2⁻¹ : ℝ) • (1 + ω)) = 0
  rw [map_smul, map_add, map_one, toH_ω]
  ext <;> simp [Algebra.algebraMap_eq_smul_one]

@[simp] lemma toH_one_pMinus : toH 1 (by ring) pMinus = 1 := by
  show toH 1 (by ring) ((2⁻¹ : ℝ) • (1 - ω)) = 1
  rw [map_smul, map_sub, map_one, toH_ω]
  ext <;> simp [Algebra.algebraMap_eq_smul_one] <;> norm_num

@[simp] lemma toH_neg_one_pPlus : toH (-1) (by ring) pPlus = 1 := by
  show toH (-1) (by ring) ((2⁻¹ : ℝ) • (1 + ω)) = 1
  rw [map_smul, map_add, map_one, toH_ω]
  ext <;> simp [Algebra.algebraMap_eq_smul_one] <;> norm_num

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

end

end Cl03QuaternionProd

end Spinor
