import Spinor.ComplexClassification
import Spinor.OrthogonalAction
import Spinor.RealClassification
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

/-- The real Clifford algebra `Cl(0,2)` is Hamilton's quaternion algebra. -/
noncomputable def realCl02EquivQuaternion :
    CliffordAlgebra realCl02Form ≃ₐ[ℝ] ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)] := by
  rw [realCl02Form_eq_quaternionQ]
  exact CliffordAlgebraQuaternion.equiv (R := ℝ) (c₁ := (-1 : ℝ)) (c₂ := (-1 : ℝ))

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
