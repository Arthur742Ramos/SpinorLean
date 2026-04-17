import Spinor.ComplexClassification
import Spinor.OrthogonalAction
import Spinor.RealClassification
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
  Concrete low-dimensional specializations of the existing complex and real Clifford
  classifications.

  These package small-dimensional cases of the general split/complex results into explicit matrix
  and product-algebra models, giving reusable algebraic entry points for the roadmap's
  low-dimensional examples.
-/

namespace Spinor

noncomputable section

open scoped Quaternion

section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

@[simp]
theorem cliffordEquivEven_apply_star (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    ((CliffordAlgebra.equivEven Q (star x) :
        CliffordAlgebra.even (CliffordAlgebra.EquivEven.Q' Q)) :
      CliffordAlgebra (CliffordAlgebra.EquivEven.Q' Q)) =
      star (CliffordAlgebra.equivEven Q x : CliffordAlgebra (CliffordAlgebra.EquivEven.Q' Q)) := by
  change ↑(CliffordAlgebra.toEven Q (star x)) =
    star (CliffordAlgebra.toEven Q x : CliffordAlgebra (CliffordAlgebra.EquivEven.Q' Q))
  rw [CliffordAlgebra.star_def, CliffordAlgebra.coe_toEven_reverse_involute, CliffordAlgebra.star_def]
  rw [CliffordAlgebra.involute_eq_of_mem_even
    (show
      (((CliffordAlgebra.toEven Q x : CliffordAlgebra.even (CliffordAlgebra.EquivEven.Q' Q)) :
          CliffordAlgebra (CliffordAlgebra.EquivEven.Q' Q)) ∈
        CliffordAlgebra.even (CliffordAlgebra.EquivEven.Q' Q)) from
      (CliffordAlgebra.toEven Q x).property)]

@[simp]
theorem cliffordEquivEven_symm_apply_star (Q : QuadraticForm R M)
    (x : CliffordAlgebra.even (CliffordAlgebra.EquivEven.Q' Q)) :
    (CliffordAlgebra.equivEven Q).symm
        ⟨star (x : CliffordAlgebra (CliffordAlgebra.EquivEven.Q' Q)), by
          simpa [CliffordAlgebra.even, CliffordAlgebra.even_toSubmodule, CliffordAlgebra.star_def,
            CliffordAlgebra.reverse_mem_evenOdd_iff, CliffordAlgebra.involute_mem_evenOdd_iff] using
            x.property⟩ =
      star ((CliffordAlgebra.equivEven Q).symm x) := by
  apply (CliffordAlgebra.equivEven Q).injective
  ext
  simp [cliffordEquivEven_apply_star]

@[simps]
def spinGroupToEven (Q : QuadraticForm R M) : spinGroup Q →* CliffordAlgebra.even Q where
  toFun x := ⟨x, spinGroup.mem_even x.prop⟩
  map_one' := by
    ext
    rfl
  map_mul' x y := by
    ext
    rfl

end

/-- The standard complex 1-dimensional quadratic form, grouped as one extra square. -/
abbrev complexCl1Form : QuadraticForm ℂ (((Fin 0 ⊕ Fin 0) → ℂ) × ℂ) :=
  complexOddForm 0

/-- The Clifford algebra of the standard complex 1-dimensional form is `ℂ × ℂ`. -/
noncomputable def complexCl1EquivProd :
    CliffordAlgebra complexCl1Form ≃ₐ[ℂ] ℂ × ℂ := by
  let e₁ : Fin (2 ^ 0) ≃ Fin 1 := Equiv.cast (by norm_num)
  let e : Fin (2 ^ 0) ≃ Unit := e₁.trans finOneEquiv
  simpa [complexCl1Form] using
    ((complexOddCliffordEquivProdMatrix 0).trans
      (AlgEquiv.prodCongr
        (Matrix.reindexAlgEquiv ℂ ℂ e)
        (Matrix.reindexAlgEquiv ℂ ℂ e))).trans
      (AlgEquiv.prodCongr
        (Matrix.uniqueAlgEquiv (R := ℂ) (A := ℂ) (m := Unit))
        (Matrix.uniqueAlgEquiv (R := ℂ) (A := ℂ) (m := Unit)))

/-- The standard complex 2-dimensional quadratic form. -/
abbrev complexCl2Form : QuadraticForm ℂ ((Fin 1 ⊕ Fin 1) → ℂ) :=
  complexSumSquares (Fin 1 ⊕ Fin 1)

/-- The Clifford algebra of the standard complex 2-dimensional form is `Mat₂(ℂ)`. -/
noncomputable def complexCl2EquivMatrix2 :
    CliffordAlgebra (complexCl2Form) ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ := by
  simpa [complexCl2Form] using complexEvenCliffordEquivMatrix 1

/-- The standard complex 3-dimensional quadratic form, grouped as a 2-dimensional even block plus
one extra square. -/
abbrev complexCl3Form : QuadraticForm ℂ (((Fin 1 ⊕ Fin 1) → ℂ) × ℂ) :=
  complexOddForm 1

/-- The Clifford algebra of the standard complex 3-dimensional form is
`Mat₂(ℂ) × Mat₂(ℂ)`. -/
noncomputable def complexCl3EquivProdMatrix2 :
    CliffordAlgebra (complexCl3Form) ≃ₐ[ℂ]
      Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ := by
  simpa [complexCl3Form] using complexOddCliffordEquivProdMatrix 1

/-- The standard complex 4-dimensional quadratic form. -/
abbrev complexCl4Form : QuadraticForm ℂ ((Fin 2 ⊕ Fin 2) → ℂ) :=
  complexSumSquares (Fin 2 ⊕ Fin 2)

/-- The Clifford algebra of the standard complex 4-dimensional form is `Mat₄(ℂ)`. -/
noncomputable def complexCl4EquivMatrix4 :
    CliffordAlgebra (complexCl4Form) ≃ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ := by
  simpa [complexCl4Form] using complexEvenCliffordEquivMatrix 2

/-- The standard real split-signature `(1,1)` form. -/
abbrev realCl11Form : QuadraticForm ℝ ((Fin 1 ⊕ Fin 1) → ℝ) :=
  standardSignatureForm 1 1

/-- The standard negative real 1-dimensional quadratic form. -/
abbrev realCl01Form : QuadraticForm ℝ ℝ :=
  CliffordAlgebraComplex.Q

/-- The real Clifford algebra `Cl(0,1)` is `ℂ`. -/
noncomputable def realCl01EquivComplex :
    CliffordAlgebra realCl01Form ≃ₐ[ℝ] ℂ := by
  simpa [realCl01Form] using CliffordAlgebraComplex.equiv

@[simp]
theorem realCl01EquivComplex_apply_star (x : CliffordAlgebra realCl01Form) :
    realCl01EquivComplex (star x) = star (realCl01EquivComplex x) := by
  change CliffordAlgebraComplex.toComplex (CliffordAlgebra.reverse (CliffordAlgebra.involute x)) =
    star (CliffordAlgebraComplex.toComplex x)
  rw [CliffordAlgebraComplex.reverse_apply, CliffordAlgebraComplex.toComplex_involute, Complex.star_def]

/-- The standard negative real 2-dimensional quadratic form on `ℝ × ℝ`. -/
abbrev realCl02Form : QuadraticForm ℝ (ℝ × ℝ) :=
  CliffordAlgebra.EquivEven.Q' realCl01Form

@[simp]
theorem realCl02Form_apply (x : ℝ × ℝ) :
    realCl02Form x = -(x.1 * x.1) - x.2 * x.2 := by
  simp [realCl02Form, realCl01Form, CliffordAlgebraComplex.Q_apply]
  ring

theorem realCl02Form_eq_quaternionQ :
    realCl02Form = CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1 : ℝ) := by
  ext v
  simp [realCl02Form, realCl01Form, CliffordAlgebra.EquivEven.Q', CliffordAlgebraComplex.Q,
    CliffordAlgebraQuaternion.Q]

/-- The standard `Cl(0,2)` form agrees with the quaternion form via the identity map. -/
noncomputable def realCl02QuaternionIsometry :
    realCl02Form.IsometryEquiv (CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1 : ℝ)) where
  toLinearEquiv := LinearEquiv.refl ℝ (ℝ × ℝ)
  map_app' v := by
    simp [realCl02Form_eq_quaternionQ]

/-- The real Clifford algebra `Cl(0,2)` is Hamilton's quaternion algebra. -/
noncomputable def realCl02EquivQuaternion :
    CliffordAlgebra realCl02Form ≃ₐ[ℝ] ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)] :=
  (CliffordAlgebra.equivOfIsometry realCl02QuaternionIsometry).trans
    (CliffordAlgebraQuaternion.equiv (R := ℝ) (c₁ := (-1 : ℝ)) (c₂ := (-1 : ℝ)))

@[simp]
theorem realCl02EquivQuaternion_apply_ι (v : ℝ × ℝ) :
    realCl02EquivQuaternion (CliffordAlgebra.ι realCl02Form v) =
      (⟨0, v.1, v.2, 0⟩ : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) := by
  simp [realCl02EquivQuaternion, realCl02QuaternionIsometry]
  constructor <;> rfl

@[simp]
theorem realCl02EquivQuaternion_apply_star (x : CliffordAlgebra realCl02Form) :
    realCl02EquivQuaternion (star x) = star (realCl02EquivQuaternion x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      simp
  | ι v =>
      simp [realCl02EquivQuaternion_apply_ι]
  | mul a b ha hb =>
      simp [ha, hb]
  | add a b ha hb =>
      simp [ha, hb]

/-- The even real Clifford algebra `Cl⁺(0,2)` is `ℂ`. -/
noncomputable def realEvenCl02EquivComplex :
    CliffordAlgebra.even realCl02Form ≃ₐ[ℝ] ℂ := by
  simpa [realCl02Form] using
    ((CliffordAlgebra.equivEven realCl01Form).symm.trans realCl01EquivComplex)

@[simp]
theorem realEvenCl02EquivComplex_apply_star (x : CliffordAlgebra.even realCl02Form) :
    realEvenCl02EquivComplex
        ⟨star (x : CliffordAlgebra realCl02Form), by
          simpa [CliffordAlgebra.even, CliffordAlgebra.even_toSubmodule, CliffordAlgebra.star_def,
            CliffordAlgebra.reverse_mem_evenOdd_iff, CliffordAlgebra.involute_mem_evenOdd_iff] using
            x.property⟩ =
      star (realEvenCl02EquivComplex x) := by
  change realCl01EquivComplex
      ((CliffordAlgebra.equivEven realCl01Form).symm
        ⟨star (x : CliffordAlgebra realCl02Form), by
          simpa [CliffordAlgebra.even, CliffordAlgebra.even_toSubmodule, CliffordAlgebra.star_def,
            CliffordAlgebra.reverse_mem_evenOdd_iff, CliffordAlgebra.involute_mem_evenOdd_iff] using
            x.property⟩) =
    star (realCl01EquivComplex ((CliffordAlgebra.equivEven realCl01Form).symm x))
  rw [cliffordEquivEven_symm_apply_star, realCl01EquivComplex_apply_star]

@[simp]
theorem realEvenCl02EquivComplex_apply_bilin (m r : ℝ) :
    realEvenCl02EquivComplex ((CliffordAlgebra.even.ι realCl02Form).bilin (0, 1) (m, r)) =
      m * Complex.I - r := by
  change
    realCl01EquivComplex
        ((CliffordAlgebra.equivEven realCl01Form).symm
          ((CliffordAlgebra.even.ι realCl02Form).bilin (0, 1) (m, r))) =
      m * Complex.I - r
  rw [show
      (CliffordAlgebra.equivEven realCl01Form).symm
          ((CliffordAlgebra.even.ι realCl02Form).bilin (0, 1) (m, r)) =
        CliffordAlgebra.ofEven realCl01Form
          ((CliffordAlgebra.even.ι realCl02Form).bilin (0, 1) (m, r)) by
      rfl]
  rw [CliffordAlgebra.ofEven_ι]
  show realCl01EquivComplex
      ((CliffordAlgebra.ι realCl01Form (0, 1).1 + algebraMap ℝ _ (0, 1).2) *
        (CliffordAlgebra.ι realCl01Form (m, r).1 - algebraMap ℝ _ (m, r).2)) =
    m * Complex.I - r
  simp only [map_zero, map_one, zero_add, one_mul, map_sub]
  have hι : realCl01EquivComplex (CliffordAlgebra.ι realCl01Form m) = m * Complex.I := by
    show CliffordAlgebraComplex.equiv (CliffordAlgebra.ι realCl01Form m) = m * Complex.I
    rw [show CliffordAlgebraComplex.equiv (CliffordAlgebra.ι realCl01Form m) =
        CliffordAlgebraComplex.toComplex (CliffordAlgebra.ι realCl01Form m) from rfl,
      CliffordAlgebraComplex.toComplex_ι]
    exact Complex.real_smul
  rw [hι, AlgEquiv.commutes]
  simp

noncomputable def spinGroupRealCl02ToComplex : spinGroup realCl02Form →* ℂ :=
  realEvenCl02EquivComplex.toMonoidHom.comp (spinGroupToEven realCl02Form)

theorem spinGroupRealCl02ToComplex_mem_unitary (x : spinGroup realCl02Form) :
    spinGroupRealCl02ToComplex x ∈ unitary ℂ := by
  rw [Unitary.mem_iff]
  let x₀ : CliffordAlgebra.even realCl02Form := (spinGroupToEven realCl02Form) x
  let xStar : CliffordAlgebra.even realCl02Form := ⟨star (x : CliffordAlgebra realCl02Form), by
    simpa [CliffordAlgebra.even, CliffordAlgebra.even_toSubmodule, CliffordAlgebra.star_def,
      CliffordAlgebra.reverse_mem_evenOdd_iff, CliffordAlgebra.involute_mem_evenOdd_iff] using
      (spinGroup.mem_even x.prop)⟩
  constructor
  · change star (realEvenCl02EquivComplex x₀) * realEvenCl02EquivComplex x₀ = 1
    rw [← realEvenCl02EquivComplex_apply_star, ← map_mul]
    have hx : xStar * x₀ = 1 := by
      ext
      exact spinGroup.coe_star_mul_self x
    change realEvenCl02EquivComplex (xStar * x₀) = 1
    rw [hx, map_one]
  · change realEvenCl02EquivComplex x₀ * star (realEvenCl02EquivComplex x₀) = 1
    rw [← realEvenCl02EquivComplex_apply_star, ← map_mul]
    have hx : x₀ * xStar = 1 := by
      ext
      exact spinGroup.coe_mul_star_self x
    change realEvenCl02EquivComplex (x₀ * xStar) = 1
    rw [hx, map_one]

/-- The spin group of the compact real 2-dimensional form, viewed as the unitary circle in `ℂ`.

Mathlib's `pinGroup` convention is normalized so vectors with `Q(v) = -1` are unitary, so the
compact `Spin(2)` model is `realCl02Form`, not `realCl20Form`.
-/
noncomputable def spinGroupRealCl02ToUnitaryComplex : spinGroup realCl02Form →* unitary ℂ :=
  (spinGroupRealCl02ToComplex).codRestrict (unitary ℂ) spinGroupRealCl02ToComplex_mem_unitary

noncomputable def realSpin02PreimageEven (z : unitary ℂ) : CliffordAlgebra.even realCl02Form :=
  (CliffordAlgebra.even.ι realCl02Form).bilin (0, 1) ((z : ℂ).im, -((z : ℂ).re))

noncomputable def unitaryComplexToSpinGroupRealCl02 (z : unitary ℂ) : spinGroup realCl02Form := by
  let m : ℝ × ℝ := ((z : ℂ).im, -((z : ℂ).re))
  have hz_complex : ((Complex.normSq (z : ℂ) : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    simpa [Complex.star_def] using (Unitary.coe_star_mul_self z : ((star z : unitary ℂ) : ℂ) * z = 1)
  have hz_norm : Complex.normSq (z : ℂ) = 1 := by
    exact Complex.ofReal_injective hz_complex
  have hm : realCl02Form m = -1 := by
    dsimp [m]
    rw [Complex.normSq_apply] at hz_norm
    ring_nf at hz_norm ⊢
    nlinarith
  have h0 : realCl02Form ((0 : ℝ), (1 : ℝ)) = -1 := by
    simp
  refine ⟨realSpin02PreimageEven z, ?_⟩
  refine ⟨?_, (realSpin02PreimageEven z).property⟩
  change
    (CliffordAlgebra.ι realCl02Form ((0 : ℝ), (1 : ℝ)) * CliffordAlgebra.ι realCl02Form m) ∈
      pinGroup realCl02Form
  exact Submonoid.mul_mem _ (iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := realCl02Form) _ h0)
    (iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := realCl02Form) _ hm)

@[simp]
theorem spinGroupRealCl02ToUnitaryComplex_apply_preimage (z : unitary ℂ) :
    spinGroupRealCl02ToUnitaryComplex (unitaryComplexToSpinGroupRealCl02 z) = z := by
  ext
  change spinGroupRealCl02ToComplex (unitaryComplexToSpinGroupRealCl02 z) = z
  change realEvenCl02EquivComplex (spinGroupToEven realCl02Form (unitaryComplexToSpinGroupRealCl02 z)) = z
  have hEven :
      spinGroupToEven realCl02Form (unitaryComplexToSpinGroupRealCl02 z) = realSpin02PreimageEven z := by
    apply Subtype.ext
    simp [spinGroupToEven, unitaryComplexToSpinGroupRealCl02, realSpin02PreimageEven]
  rw [hEven, realSpin02PreimageEven, realEvenCl02EquivComplex_apply_bilin]
  apply Complex.ext <;> simp

theorem spinGroupRealCl02ToUnitaryComplex_injective :
    Function.Injective spinGroupRealCl02ToUnitaryComplex := by
  intro x y h
  have h' : spinGroupRealCl02ToComplex x = spinGroupRealCl02ToComplex y := congrArg Subtype.val h
  have hEven : spinGroupToEven realCl02Form x = spinGroupToEven realCl02Form y := by
    apply realEvenCl02EquivComplex.injective
    simpa [spinGroupRealCl02ToComplex] using h'
  apply Subtype.ext
  simpa [spinGroupToEven] using congrArg Subtype.val hEven

/-- The compact 2-dimensional real spin group is the unitary circle in `ℂ`. -/
noncomputable def realSpin02EquivUnitaryComplex :
    spinGroup realCl02Form ≃* unitary ℂ :=
  MulEquiv.ofBijective spinGroupRealCl02ToUnitaryComplex
    ⟨spinGroupRealCl02ToUnitaryComplex_injective, fun z => ⟨unitaryComplexToSpinGroupRealCl02 z,
      spinGroupRealCl02ToUnitaryComplex_apply_preimage z⟩⟩

/-- The standard positive real 2-dimensional quadratic form on `ℝ × ℝ`. -/
abbrev realCl20Form : QuadraticForm ℝ (ℝ × ℝ) :=
  -realCl02Form

/-- The even real Clifford algebra `Cl⁺(2,0)` is `ℂ`. -/
noncomputable def realEvenCl20EquivComplex :
    CliffordAlgebra.even realCl20Form ≃ₐ[ℝ] ℂ := by
  simpa [realCl20Form, realCl02Form, realCl01Form] using
    (((CliffordAlgebra.evenEquivEvenNeg (Q := realCl02Form)).symm.trans
      (CliffordAlgebra.equivEven realCl01Form).symm).trans
      realCl01EquivComplex)

/-- The standard negative real 3-dimensional quadratic form on `((ℝ × ℝ) × ℝ)`. -/
abbrev realCl03Form : QuadraticForm ℝ ((ℝ × ℝ) × ℝ) :=
  CliffordAlgebra.EquivEven.Q' realCl02Form

@[simp]
theorem realCl03Form_apply (x : ((ℝ × ℝ) × ℝ)) :
    realCl03Form x = -(x.1.1 * x.1.1) - x.1.2 * x.1.2 - x.2 * x.2 := by
  obtain ⟨⟨x1, x2⟩, x3⟩ := x
  simp [realCl03Form]
  ring

/-- The standard positive real 3-dimensional quadratic form on `((ℝ × ℝ) × ℝ)`. -/
abbrev realCl30Form : QuadraticForm ℝ ((ℝ × ℝ) × ℝ) :=
  -realCl03Form

/-- The even real Clifford algebra `Cl⁺(3,0)` is Hamilton's quaternion algebra. -/
noncomputable def realEvenCl30EquivQuaternion :
    CliffordAlgebra.even realCl30Form ≃ₐ[ℝ] ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)] := by
  simpa [realCl30Form, realCl03Form, realCl02Form] using
    (((CliffordAlgebra.evenEquivEvenNeg (Q := realCl03Form)).symm.trans
      (CliffordAlgebra.equivEven realCl02Form).symm).trans
      realCl02EquivQuaternion)

/-- The even real Clifford algebra `Cl⁺(0,3)` is Hamilton's quaternion algebra.

Unlike `realEvenCl30EquivQuaternion`, this version works with the negative-signature form
`realCl03Form`, which is the form used by `pinGroup` / `spinGroup` for the compact Spin(3). -/
noncomputable def realEvenCl03EquivQuaternion :
    CliffordAlgebra.even realCl03Form ≃ₐ[ℝ] ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)] := by
  simpa [realCl03Form] using
    ((CliffordAlgebra.equivEven realCl02Form).symm.trans realCl02EquivQuaternion)

@[simp]
theorem realEvenCl03EquivQuaternion_apply_star (x : CliffordAlgebra.even realCl03Form) :
    realEvenCl03EquivQuaternion
        ⟨star (x : CliffordAlgebra realCl03Form), by
          simpa [CliffordAlgebra.even, CliffordAlgebra.even_toSubmodule, CliffordAlgebra.star_def,
            CliffordAlgebra.reverse_mem_evenOdd_iff, CliffordAlgebra.involute_mem_evenOdd_iff] using
            x.property⟩ =
      star (realEvenCl03EquivQuaternion x) := by
  change realCl02EquivQuaternion
      ((CliffordAlgebra.equivEven realCl02Form).symm
        ⟨star (x : CliffordAlgebra realCl03Form), by
          simpa [CliffordAlgebra.even, CliffordAlgebra.even_toSubmodule, CliffordAlgebra.star_def,
            CliffordAlgebra.reverse_mem_evenOdd_iff, CliffordAlgebra.involute_mem_evenOdd_iff] using
            x.property⟩) =
    star (realCl02EquivQuaternion ((CliffordAlgebra.equivEven realCl02Form).symm x))
  rw [cliffordEquivEven_symm_apply_star, realCl02EquivQuaternion_apply_star]

@[simp]
theorem realEvenCl03EquivQuaternion_apply_bilin
    (x y : ((ℝ × ℝ) × ℝ)) :
    realEvenCl03EquivQuaternion ((CliffordAlgebra.even.ι realCl03Form).bilin x y) =
      (⟨-(x.1.1 * y.1.1 + x.1.2 * y.1.2 + x.2 * y.2),
        x.2 * y.1.1 - x.1.1 * y.2,
        x.2 * y.1.2 - x.1.2 * y.2,
        x.1.1 * y.1.2 - x.1.2 * y.1.1⟩ :
        ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) := by
  obtain ⟨⟨x1, x2⟩, x3⟩ := x
  obtain ⟨⟨y1, y2⟩, y3⟩ := y
  change
    realCl02EquivQuaternion
        ((CliffordAlgebra.equivEven realCl02Form).symm
          ((CliffordAlgebra.even.ι realCl03Form).bilin ((x1, x2), x3) ((y1, y2), y3))) =
      _
  rw [show
      (CliffordAlgebra.equivEven realCl02Form).symm
          ((CliffordAlgebra.even.ι realCl03Form).bilin ((x1, x2), x3) ((y1, y2), y3)) =
        CliffordAlgebra.ofEven realCl02Form
          ((CliffordAlgebra.even.ι realCl03Form).bilin ((x1, x2), x3) ((y1, y2), y3)) by
      rfl]
  rw [CliffordAlgebra.ofEven_ι]
  ext <;> simp [realCl02EquivQuaternion_apply_ι] <;> ring

noncomputable def spinGroupRealCl03ToQuaternion :
    spinGroup realCl03Form →* ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)] :=
  realEvenCl03EquivQuaternion.toMonoidHom.comp (spinGroupToEven realCl03Form)

theorem spinGroupRealCl03ToQuaternion_mem_unitary (x : spinGroup realCl03Form) :
    spinGroupRealCl03ToQuaternion x ∈ unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)] := by
  rw [Unitary.mem_iff]
  let x₀ : CliffordAlgebra.even realCl03Form := spinGroupToEven realCl03Form x
  let xStar : CliffordAlgebra.even realCl03Form := ⟨star (x : CliffordAlgebra realCl03Form), by
    simpa [CliffordAlgebra.even, CliffordAlgebra.even_toSubmodule, CliffordAlgebra.star_def,
      CliffordAlgebra.reverse_mem_evenOdd_iff, CliffordAlgebra.involute_mem_evenOdd_iff] using
      (spinGroup.mem_even x.prop)⟩
  constructor
  · change star (realEvenCl03EquivQuaternion x₀) * realEvenCl03EquivQuaternion x₀ = 1
    rw [← realEvenCl03EquivQuaternion_apply_star, ← map_mul]
    have hx : xStar * x₀ = 1 := by
      ext
      exact spinGroup.coe_star_mul_self x
    change realEvenCl03EquivQuaternion (xStar * x₀) = 1
    rw [hx, map_one]
  · change realEvenCl03EquivQuaternion x₀ * star (realEvenCl03EquivQuaternion x₀) = 1
    rw [← realEvenCl03EquivQuaternion_apply_star, ← map_mul]
    have hx : x₀ * xStar = 1 := by
      ext
      exact spinGroup.coe_mul_star_self x
    change realEvenCl03EquivQuaternion (x₀ * xStar) = 1
    rw [hx, map_one]

noncomputable def spinGroupRealCl03ToUnitaryQuaternion :
    spinGroup realCl03Form →* unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)] :=
  (spinGroupRealCl03ToQuaternion).codRestrict
    (unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) spinGroupRealCl03ToQuaternion_mem_unitary

theorem spinGroupRealCl03ToUnitaryQuaternion_injective :
    Function.Injective spinGroupRealCl03ToUnitaryQuaternion := by
  intro x y h
  have h' : spinGroupRealCl03ToQuaternion x = spinGroupRealCl03ToQuaternion y := congrArg Subtype.val h
  have hEven : spinGroupToEven realCl03Form x = spinGroupToEven realCl03Form y := by
    apply realEvenCl03EquivQuaternion.injective
    simpa [spinGroupRealCl03ToQuaternion] using h'
  apply Subtype.ext
  simpa [spinGroupToEven] using congrArg Subtype.val hEven

theorem unitaryQuaternion_normSq_eq_one (q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
    Quaternion.normSq (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) = 1 := by
  have hstar :
      (star q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) * q =
        (((Quaternion.normSq (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)])) : ℝ) :
          ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) := by
    simpa using Quaternion.star_mul_self (a := (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]))
  have hnorm_coe :
      (((Quaternion.normSq (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)])) : ℝ) :
        ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) = 1 := by
    exact hstar.symm.trans (Unitary.coe_star_mul_self q)
  apply Quaternion.coe_injective
  exact hnorm_coe

theorem unitaryQuaternion_sqSum_eq_one (q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
    (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).re ^ 2 +
      (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imI ^ 2 +
      (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imJ ^ 2 +
      (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imK ^ 2 = 1 := by
  simpa [Quaternion.normSq_def'] using unitaryQuaternion_normSq_eq_one q

/-- Convert a slice quaternion `a + bi + cj` into the corresponding left unit vector data. -/
abbrev quaternionLeftVector (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) : ((ℝ × ℝ) × ℝ) :=
  ((q.imI, q.imJ), q.re)

/-- Convert a slice quaternion `a + bi + cj` into the corresponding right unit vector data. -/
abbrev quaternionRightVector (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) : ((ℝ × ℝ) × ℝ) :=
  ((q.imI, q.imJ), -q.re)

theorem realCl03Form_leftVector_eq_neg_one
    (q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)])
    (hk : (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imK = 0) :
    realCl03Form (quaternionLeftVector (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)])) = -1 := by
  rw [realCl03Form_apply]
  have hq := unitaryQuaternion_sqSum_eq_one q
  nlinarith [hq, hk]

theorem realCl03Form_rightVector_eq_neg_one
    (q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)])
    (hk : (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imK = 0) :
    realCl03Form (quaternionRightVector (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)])) = -1 := by
  rw [realCl03Form_apply]
  have hq := unitaryQuaternion_sqSum_eq_one q
  nlinarith [hq, hk]

theorem realEvenCl03EquivQuaternion_apply_bilin_slice
    (p r : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)])
    (hp : (p : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imK = 0)
    (hr : (r : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imK = 0) :
    realEvenCl03EquivQuaternion
        ((CliffordAlgebra.even.ι realCl03Form).bilin
          (quaternionLeftVector (p : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]))
          (quaternionRightVector (r : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]))) =
      ((p : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) * r :
        ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) := by
  ext <;> simp [realEvenCl03EquivQuaternion_apply_bilin, hp, hr] <;> ring

noncomputable def realSpin03LeftSlice
    (q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
    unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)] := by
  by_cases h : (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imJ = 0 ∧
      (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imK = 0
  · exact 1
  · let c : ℝ := (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imJ
    let d : ℝ := (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imK
    let s : ℝ := Real.sqrt (c ^ 2 + d ^ 2)
    have hs_sq : s ^ 2 = c ^ 2 + d ^ 2 := by
      dsimp [s]
      nlinarith [Real.sq_sqrt (show 0 ≤ c ^ 2 + d ^ 2 by positivity)]
    have hs : s ≠ 0 := by
      intro hs
      apply h
      constructor <;> nlinarith [hs_sq]
    refine ⟨⟨c / s, d / s, 0, 0⟩, ?_⟩
    have hsum : c / s * (c / s) + d / s * (d / s) = 1 := by
      field_simp [hs]
      nlinarith [hs_sq]
    rw [Unitary.mem_iff]
    constructor
    · ext <;> simp [hsum] <;> ring
    · ext <;> simp [hsum] <;> ring

noncomputable def realSpin03RightSlice
    (q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
    unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)] :=
  star (realSpin03LeftSlice q) * q

@[simp]
theorem realSpin03LeftSlice_imK
    (q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
    ((realSpin03LeftSlice q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
        ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imK = 0 := by
  by_cases h : (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imJ = 0 ∧
      (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imK = 0
  · simp [realSpin03LeftSlice, h]
  · simp [realSpin03LeftSlice, h]

@[simp]
theorem realSpin03RightSlice_imK
    (q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
    ((realSpin03RightSlice q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
        ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imK = 0 := by
  by_cases h : (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imJ = 0 ∧
      (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imK = 0
  · simp [realSpin03RightSlice, realSpin03LeftSlice, h]
  · let a : ℝ := (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).re
    let b : ℝ := (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imI
    let c : ℝ := (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imJ
    let d : ℝ := (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]).imK
    let s : ℝ := Real.sqrt (c ^ 2 + d ^ 2)
    have hs_sq : s ^ 2 = c ^ 2 + d ^ 2 := by
      dsimp [s]
      nlinarith [Real.sq_sqrt (show 0 ≤ c ^ 2 + d ^ 2 by positivity)]
    have hs : s ≠ 0 := by
      intro hs
      apply h
      constructor <;> nlinarith [hs_sq]
    simp [realSpin03RightSlice, realSpin03LeftSlice, h]
    field_simp [hs]
    ring

theorem realSpin03LeftSlice_mul_rightSlice
    (q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
    (((realSpin03LeftSlice q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
        ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) *
      ((realSpin03RightSlice q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
        ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)])) =
      (q : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) := by
  have hmul : realSpin03LeftSlice q * realSpin03RightSlice q = q := by
    calc
      realSpin03LeftSlice q * realSpin03RightSlice q =
          realSpin03LeftSlice q * (star (realSpin03LeftSlice q) * q) := by
            rfl
      _ = (realSpin03LeftSlice q * star (realSpin03LeftSlice q)) * q := by
            rw [mul_assoc]
      _ = 1 * q := by rw [Unitary.mul_star_self]
      _ = q := by simp
  exact congrArg Subtype.val hmul

noncomputable def realSpin03PreimageEven
    (q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
    CliffordAlgebra.even realCl03Form :=
  (CliffordAlgebra.even.ι realCl03Form).bilin
    (quaternionLeftVector
      ((realSpin03LeftSlice q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
        ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]))
    (quaternionRightVector
      ((realSpin03RightSlice q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
        ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]))

noncomputable def unitaryQuaternionToSpinGroupRealCl03
    (q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
    spinGroup realCl03Form := by
  have hLeft : realCl03Form
      (quaternionLeftVector
        ((realSpin03LeftSlice q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
          ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)])) = -1 :=
    realCl03Form_leftVector_eq_neg_one (realSpin03LeftSlice q) (realSpin03LeftSlice_imK q)
  have hRight : realCl03Form
      (quaternionRightVector
        ((realSpin03RightSlice q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
          ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)])) = -1 :=
    realCl03Form_rightVector_eq_neg_one (realSpin03RightSlice q) (realSpin03RightSlice_imK q)
  refine ⟨realSpin03PreimageEven q, ?_⟩
  refine ⟨?_, (realSpin03PreimageEven q).property⟩
  change
    (CliffordAlgebra.ι realCl03Form
        (quaternionLeftVector
          ((realSpin03LeftSlice q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
            ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)])) *
      CliffordAlgebra.ι realCl03Form
        (quaternionRightVector
          ((realSpin03RightSlice q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
            ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]))) ∈
      pinGroup realCl03Form
  exact Submonoid.mul_mem _
    (iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := realCl03Form)
      (quaternionLeftVector
        ((realSpin03LeftSlice q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
          ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)])) hLeft)
    (iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := realCl03Form)
      (quaternionRightVector
        ((realSpin03RightSlice q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
          ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)])) hRight)

@[simp]
theorem spinGroupRealCl03ToUnitaryQuaternion_apply_preimage
    (q : unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) :
    spinGroupRealCl03ToUnitaryQuaternion (unitaryQuaternionToSpinGroupRealCl03 q) = q := by
  apply Subtype.ext
  change
    realEvenCl03EquivQuaternion
      (spinGroupToEven realCl03Form (unitaryQuaternionToSpinGroupRealCl03 q)) = (q :
        ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)])
  have hEven :
      spinGroupToEven realCl03Form (unitaryQuaternionToSpinGroupRealCl03 q) = realSpin03PreimageEven q := by
    apply Subtype.ext
    simp [spinGroupToEven, unitaryQuaternionToSpinGroupRealCl03, realSpin03PreimageEven]
  rw [hEven, realSpin03PreimageEven, realEvenCl03EquivQuaternion_apply_bilin_slice
    (realSpin03LeftSlice q) (realSpin03RightSlice q)
    (realSpin03LeftSlice_imK q) (realSpin03RightSlice_imK q)]
  exact realSpin03LeftSlice_mul_rightSlice q

/-- The compact 3-dimensional real spin group is the unitary quaternion group. -/
noncomputable def realSpin03EquivUnitaryQuaternion :
    spinGroup realCl03Form ≃* unitary ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)] :=
  MulEquiv.ofBijective spinGroupRealCl03ToUnitaryQuaternion
    ⟨spinGroupRealCl03ToUnitaryQuaternion_injective, fun q =>
      ⟨unitaryQuaternionToSpinGroupRealCl03 q,
        spinGroupRealCl03ToUnitaryQuaternion_apply_preimage q⟩⟩

/-- The standard negative real 4-dimensional quadratic form on `(((ℝ × ℝ) × ℝ) × ℝ)`. -/
abbrev realCl04Form : QuadraticForm ℝ (((ℝ × ℝ) × ℝ) × ℝ) :=
  CliffordAlgebra.EquivEven.Q' realCl03Form

/-- The even real Clifford algebra `Cl⁺(0,4)` is isomorphic to the full Clifford
algebra `Cl(0,3)` via Mathlib's `CliffordAlgebra.equivEven`.

This is the standard "drop one negative-signature dimension into the even part"
identification and is the algebraic entry point for the classical
`Cl⁺(0,4) ≃ ℍ × ℍ` identification (which further requires `Cl(0,3) ≃ ℍ × ℍ`,
a classical fact currently outside the Mathlib library). -/
noncomputable def realEvenCl04EquivCl03 :
    CliffordAlgebra.even realCl04Form ≃ₐ[ℝ] CliffordAlgebra realCl03Form :=
  (CliffordAlgebra.equivEven realCl03Form).symm

/-- The real Clifford algebra `Cl(1,1)` is `Mat₂(ℝ)`. -/
noncomputable def realCl11EquivMatrix2 :
    CliffordAlgebra realCl11Form ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ := by
  simpa [realCl11Form] using realClifford_1_1_equivMatrix2

/-- The even real Clifford algebra `Cl⁺(1,1)` is `ℝ × ℝ`. -/
noncomputable def realEvenCl11EquivProd :
    CliffordAlgebra.even realCl11Form ≃ₐ[ℝ] ℝ × ℝ := by
  let e₁ : Fin (2 ^ (1 - 1)) ≃ Fin 1 := Equiv.cast (by norm_num)
  let e : Fin (2 ^ (1 - 1)) ≃ Unit := e₁.trans finOneEquiv
  simpa [realCl11Form] using
    ((realSplitEvenCliffordEquivProdMatrix 1 (by decide)).trans
      (AlgEquiv.prodCongr
        (Matrix.reindexAlgEquiv ℝ ℝ e)
        (Matrix.reindexAlgEquiv ℝ ℝ e))).trans
      (AlgEquiv.prodCongr
        (Matrix.uniqueAlgEquiv (R := ℝ) (A := ℝ) (m := Unit))
        (Matrix.uniqueAlgEquiv (R := ℝ) (A := ℝ) (m := Unit)))

/-- The standard real split-signature `(2,2)` form. -/
abbrev realCl22Form : QuadraticForm ℝ ((Fin 2 ⊕ Fin 2) → ℝ) :=
  standardSignatureForm 2 2

/-- The real Clifford algebra `Cl(2,2)` is `Mat₄(ℝ)`. -/
noncomputable def realCl22EquivMatrix4 :
    CliffordAlgebra realCl22Form ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ := by
  simpa [realCl22Form] using realSplitCliffordEquivMatrix 2

/-- The even real Clifford algebra `Cl⁺(2,2)` is `Mat₂(ℝ) × Mat₂(ℝ)`. -/
noncomputable def realEvenCl22EquivProdMatrix2 :
    CliffordAlgebra.even realCl22Form ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ := by
  simpa [realCl22Form] using realSplitEvenCliffordEquivProdMatrix 2 (by decide)

end

end Spinor
