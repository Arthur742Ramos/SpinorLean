import Spinor.ProdNeg
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs

/-!
  First real low-signature classification steps toward Bott periodicity.

  This file packages the standard signature forms over `ℝ` and records the basic split case
  `Cl(1,1) ≃ Mat₂(ℝ)` by reducing to the doubled-form classification already proved in
  `Spinor.ProdNeg`.
-/

namespace Spinor

noncomputable section

/-- The standard positive sum-of-squares quadratic form over `ℝ`. -/
abbrev realSumSquares (ι : Type*) [Fintype ι] : QuadraticForm ℝ (ι → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)

/-- Standard real sum-of-squares forms are nondegenerate. -/
theorem realSumSquares_nondegenerate (ι : Type*) [Fintype ι] :
    (realSumSquares ι).Nondegenerate := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, QuadraticForm.radical_weightedSumSquares]
  ext x
  constructor
  · intro hx
    ext i
    exact (Pi.mem_spanSubset_iff.mp hx) i (by simp)
  · intro hx
    rw [hx]
    simp

/-- The standard real signature-`(p, q)` quadratic form with `p` positive and `q` negative
squares. -/
abbrev standardSignatureForm (p q : ℕ) : QuadraticForm ℝ ((Fin p ⊕ Fin q) → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ
    (Sum.elim (fun _ : Fin p => (1 : ℝ)) (fun _ : Fin q => (-1 : ℝ)))

/-- Standard real signature forms are nondegenerate. -/
theorem standardSignatureForm_nondegenerate (p q : ℕ) :
    (standardSignatureForm p q).Nondegenerate := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, QuadraticForm.radical_weightedSumSquares]
  ext x
  constructor
  · intro hx
    ext i
    exact (Pi.mem_spanSubset_iff.mp hx) i (by cases i <;> simp)
  · intro hx
    rw [hx]
    simp

/-- The split form `Q ⊕ (-Q)` on coordinate sum spaces is the corresponding weighted real
signature form. -/
theorem realSumSquares_prodNeg_comp_sumArrowLequivProdArrow
    (ι κ : Type*) [Fintype ι] [Fintype κ] :
    (((realSumSquares ι).prod (-realSumSquares κ)).comp
        (LinearEquiv.sumArrowLequivProdArrow ι κ ℝ ℝ)) =
      QuadraticMap.weightedSumSquares ℝ
        (Sum.elim (fun _ : ι => (1 : ℝ)) (fun _ : κ => (-1 : ℝ))) := by
  refine QuadraticMap.ext fun x => ?_
  simp [realSumSquares, QuadraticMap.weightedSumSquares_apply]

/-- The standard split-signature `(n,n)` form is the standard `Q ⊕ (-Q)` form on an
`n`-dimensional positive quadratic space. -/
theorem standardSignatureForm_n_n_comp_sumArrowLequivProdArrow (n : ℕ) :
    (((realSumSquares (Fin n)).prod (-realSumSquares (Fin n))).comp
        (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n) ℝ ℝ)) =
      standardSignatureForm n n := by
  simpa [standardSignatureForm] using
    realSumSquares_prodNeg_comp_sumArrowLequivProdArrow (Fin n) (Fin n)

/-- The standard real split-signature `(n,n)` form is explicitly split. -/
noncomputable def realSplitIsometry (n : ℕ) :
    (standardSignatureForm n n).IsometryEquiv
      ((realSumSquares (Fin n)).prod (-realSumSquares (Fin n))) := by
  simpa [standardSignatureForm_n_n_comp_sumArrowLequivProdArrow] using
    (QuadraticMap.isometryEquivOfCompLinearEquiv
      ((realSumSquares (Fin n)).prod (-realSumSquares (Fin n)))
      (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n) ℝ ℝ)).symm

/-- The real split Clifford algebra `Cl(n,n)` is a full real matrix algebra. -/
noncomputable def realSplitCliffordEquivMatrix (n : ℕ) :
    CliffordAlgebra (standardSignatureForm n n) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hfin : Module.finrank ℝ (Fin n → ℝ) = n := by
    simpa using (Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin n))
  let e : Fin (2 ^ Module.finrank ℝ (Fin n → ℝ)) ≃ Fin (2 ^ n) :=
    Equiv.cast (by rw [hfin])
  exact
    ((CliffordAlgebra.equivOfIsometry (realSplitIsometry n)).trans
      (prodNegCliffordEquivMatrix (K := ℝ) (V := Fin n → ℝ)
        (realSumSquares (Fin n)) (realSumSquares_nondegenerate (Fin n)))).trans
      (Matrix.reindexAlgEquiv ℝ ℝ e)

/-- The even real split Clifford algebra `Cl⁺(n,n)` is a product of two full real matrix
algebras. -/
noncomputable def realSplitEvenCliffordEquivProdMatrix (n : ℕ) (hn : 0 < n) :
    CliffordAlgebra.even (standardSignatureForm n n) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ (n - 1))) (Fin (2 ^ (n - 1))) ℝ ×
        Matrix (Fin (2 ^ (n - 1))) (Fin (2 ^ (n - 1))) ℝ := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hfin : Module.finrank ℝ (Fin n → ℝ) = n := by
    simpa using (Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin n))
  have hV : 0 < Module.finrank ℝ (Fin n → ℝ) := by
    rw [hfin]
    exact hn
  let e : Fin (2 ^ (Module.finrank ℝ (Fin n → ℝ) - 1)) ≃ Fin (2 ^ (n - 1)) :=
    Equiv.cast (by rw [hfin])
  exact ((evenCliffordEquivOfIsometry (realSplitIsometry n)).trans
    (evenProdNegCliffordEquivProdMatrix (K := ℝ) (V := Fin n → ℝ)
      (realSumSquares (Fin n)) (realSumSquares_nondegenerate (Fin n)) hV)).trans
    (AlgEquiv.prodCongr (Matrix.reindexAlgEquiv ℝ ℝ e) (Matrix.reindexAlgEquiv ℝ ℝ e))

/-- The standard real `(1,1)` form is explicitly split. -/
noncomputable def realCl11SplitIsometry :
    (standardSignatureForm 1 1).IsometryEquiv
      ((realSumSquares (Fin 1)).prod (-realSumSquares (Fin 1))) :=
  realSplitIsometry 1

/-- The real Clifford algebra `Cl(1,1)` is the full `2 × 2` real matrix algebra. -/
noncomputable def realClifford_1_1_equivMatrix2 :
    CliffordAlgebra (standardSignatureForm 1 1) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ := by
  simpa using realSplitCliffordEquivMatrix 1

/-!
## Canonical low-signature entries in the real classification table

These entries package the standard negative-definite `Cl(0,n)` Clifford algebras
as algebra isomorphisms against their classical targets, starting the row
`Cl(0,1) ≃ ℂ`, `Cl(0,2) ≃ ℍ` of the real classification table that underlies
the Bott-period-8 theorem (ROADMAP §4.1).

They are named inside the dedicated `Spinor.RealClassification` namespace so the
`Spinor.RealClassification` module is the source of truth for future Bott-period
work, independent of — and compatible with — the concrete low-dimensional models
in `Spinor.LowDimensional`.
-/

namespace RealClassification

open scoped Quaternion

/-- Canonical quadratic form for `Cl(0,1)` — the unit negative square on `ℝ`. -/
abbrev Q_0_1 : QuadraticForm ℝ ℝ := CliffordAlgebraComplex.Q

/-- Canonical real-classification entry: `Cl(0,1) ≃ ℂ`. -/
noncomputable def cl_0_1_equivComplex :
    CliffordAlgebra Q_0_1 ≃ₐ[ℝ] ℂ :=
  CliffordAlgebraComplex.equiv

/-- Canonical quadratic form for `Cl(0,2)` — two unit negative squares on `ℝ × ℝ`. -/
abbrev Q_0_2 : QuadraticForm ℝ (ℝ × ℝ) :=
  CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1 : ℝ)

/-- Canonical real-classification entry: `Cl(0,2) ≃ ℍ`, Hamilton's quaternion algebra. -/
noncomputable def cl_0_2_equivQuaternion :
    CliffordAlgebra Q_0_2 ≃ₐ[ℝ] ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)] :=
  CliffordAlgebraQuaternion.equiv (R := ℝ) (c₁ := (-1 : ℝ)) (c₂ := (-1 : ℝ))

/-!
Further canonical real-classification entries `Cl(0,3) ≃ ℍ × ℍ` and
`Cl⁺(0,4) ≃ ℍ × ℍ` live in `Spinor.Cl03QuaternionProd` (as
`realCl03EquivQuaternionProd` and `realEvenCl04EquivQuaternionProd`),
which is downstream of `Spinor.LowDimensional` and therefore cannot be
imported here without creating a cycle. The forms used there are
`realCl03Form` and `realCl04Form` from `Spinor.LowDimensional`.
-/

end RealClassification

end

end Spinor
