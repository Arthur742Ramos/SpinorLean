import Spinor.OddClassification
import Spinor.ProdNeg
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Pi

/-!
  Complex Clifford classification via the split and doubled models.

  The first tractable complex case is even dimension: the standard sum-of-squares form on
  `Fin n ⊕ Fin n` is isometric to `Q ⊕ (-Q)` by scaling the second half by `i`, so the doubled
  classification from `Spinor.ProdNeg` yields the matrix form.
-/

open QuadraticMap

namespace Spinor

noncomputable section

/-- The standard complex sum-of-squares quadratic form on a coordinate space. -/
abbrev complexSumSquares (ι : Type*) [Fintype ι] : QuadraticForm ℂ (ι → ℂ) :=
  QuadraticMap.weightedSumSquares ℂ (1 : ι → ℂ)

theorem complexSumSquares_nondegenerate (ι : Type*) [Fintype ι] :
    (complexSumSquares ι).Nondegenerate := by
  classical
  letI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, QuadraticForm.radical_weightedSumSquares]
  ext x
  constructor
  · intro hx
    ext i
    exact (Pi.mem_spanSubset_iff.mp hx) i (by simp)
  · intro hx
    rw [hx]
    simp [Pi.mem_spanSubset_iff]

theorem complexSumSquares_prod_comp_sumArrowLequivProdArrow
    (ι κ : Type*) [Fintype ι] [Fintype κ] :
    (((complexSumSquares ι).prod (complexSumSquares κ)).comp
        (LinearEquiv.sumArrowLequivProdArrow ι κ ℂ ℂ)) =
      complexSumSquares (ι ⊕ κ) := by
  refine QuadraticMap.ext fun x => ?_
  simp [complexSumSquares, QuadraticMap.weightedSumSquares_apply]

theorem complexSumSquares_prodNeg_comp_sumArrowLequivProdArrow
    (ι κ : Type*) [Fintype ι] [Fintype κ] :
    (((complexSumSquares ι).prod (-complexSumSquares κ)).comp
        (LinearEquiv.sumArrowLequivProdArrow ι κ ℂ ℂ)) =
      QuadraticMap.weightedSumSquares ℂ
        (Sum.elim (fun _ : ι => (1 : ℂ)) (fun _ : κ => (-1 : ℂ))) := by
  refine QuadraticMap.ext fun x => ?_
  simp [complexSumSquares, QuadraticMap.weightedSumSquares_apply]

/-- Scaling the second half by `i` turns the standard even-dimensional complex sum of squares into a
split `Q ⊕ (-Q)` form. -/
noncomputable def complexEvenSplitIsometry (n : ℕ) :
    (complexSumSquares (Fin n ⊕ Fin n)).IsometryEquiv
      ((complexSumSquares (Fin n)).prod (-complexSumSquares (Fin n))) := by
  let unitI : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
  let splitIso :
      (complexSumSquares (Fin n ⊕ Fin n)).IsometryEquiv
        (QuadraticMap.weightedSumSquares ℂ
          (Sum.elim (fun _ : Fin n => (1 : ℂ)) (fun _ : Fin n => (-1 : ℂ)))) :=
    QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares
      (u := Sum.elim (fun _ : Fin n => (1 : ℂˣ)) (fun _ : Fin n => unitI))
      (w := (1 : (Fin n ⊕ Fin n) → ℂ))
      (w' := Sum.elim (fun _ : Fin n => (1 : ℂ)) (fun _ : Fin n => (-1 : ℂ)))
      (by
        intro i
        cases i <;> simp [unitI, Complex.I_sq, pow_two])
  let prodIso :
      ((complexSumSquares (Fin n)).prod (-complexSumSquares (Fin n))).IsometryEquiv
        (QuadraticMap.weightedSumSquares ℂ
          (Sum.elim (fun _ : Fin n => (1 : ℂ)) (fun _ : Fin n => (-1 : ℂ)))) := by
    simpa [complexSumSquares_prodNeg_comp_sumArrowLequivProdArrow]
      using
        (QuadraticMap.isometryEquivOfCompLinearEquiv
          ((complexSumSquares (Fin n)).prod (-complexSumSquares (Fin n)))
          (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n) ℂ ℂ))
  exact splitIso.trans prodIso.symm

/-- Even-dimensional complex Clifford algebras in the standard split coordinate form are full matrix
algebras. -/
noncomputable def complexEvenCliffordEquivMatrix (n : ℕ) :
    CliffordAlgebra (complexSumSquares (Fin n ⊕ Fin n)) ≃ₐ[ℂ]
      Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := by
  letI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  have hfin : Module.finrank ℂ (Fin n → ℂ) = n := by
    simpa using (Module.finrank_fintype_fun_eq_card (R := ℂ) (η := Fin n))
  let e : Fin (2 ^ Module.finrank ℂ (Fin n → ℂ)) ≃ Fin (2 ^ n) :=
    Equiv.cast (by rw [hfin])
  exact
    ((CliffordAlgebra.equivOfIsometry (complexEvenSplitIsometry n)).trans
      (prodNegCliffordEquivMatrix (K := ℂ) (V := Fin n → ℂ)
        (complexSumSquares (Fin n)) (complexSumSquares_nondegenerate (ι := Fin n)))).trans
      (Matrix.reindexAlgEquiv ℂ ℂ e)

/-- The standard odd-dimensional complex sum-of-squares form, grouped as an even part plus one
square. -/
abbrev complexOddForm (n : ℕ) : QuadraticForm ℂ (((Fin n ⊕ Fin n) → ℂ) × ℂ) :=
  (complexSumSquares (Fin n ⊕ Fin n)).prod (QuadraticMap.sq (R := ℂ))

/-- The standard odd-dimensional complex form is isometric to the odd split form built from the
diagonal isotropic space of the doubled even-dimensional part. -/
noncomputable def complexOddSplitIsometry (n : ℕ) :
    (complexOddForm n).IsometryEquiv
      (oddSplitForm (K := ℂ)
        (diagSubmodule (K := ℂ) (V := Fin n → ℂ))) := by
  letI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  let Q : QuadraticForm ℂ (Fin n → ℂ) := complexSumSquares (Fin n)
  let hQ : Q.Nondegenerate := complexSumSquares_nondegenerate (ι := Fin n)
  exact
    ((complexEvenSplitIsometry n).prod (QuadraticMap.IsometryEquiv.refl _)).trans
      ((prodNegSplitIsometry (K := ℂ) (V := Fin n → ℂ) Q hQ).prod
        (QuadraticMap.IsometryEquiv.refl _))

/-- Odd-dimensional complex Clifford algebras in the standard grouped coordinate form are products
of two full matrix algebras. -/
noncomputable def complexOddCliffordEquivProdMatrix (n : ℕ) :
    CliffordAlgebra (complexOddForm n) ≃ₐ[ℂ]
      Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ ×
        Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := by
  letI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  let M := diagSubmodule (K := ℂ) (V := Fin n → ℂ)
  have hfinM : Module.finrank ℂ M = n := by
    simpa [M, Fintype.card_fin] using
      (finrank_diagSubmodule (K := ℂ) (V := Fin n → ℂ)).trans
        (Module.finrank_fintype_fun_eq_card (R := ℂ) (η := Fin n))
  let e : Fin (2 ^ Module.finrank ℂ M) ≃ Fin (2 ^ n) :=
    Equiv.cast (by rw [hfinM])
  exact
    ((CliffordAlgebra.equivOfIsometry (complexOddSplitIsometry n)).trans
      (oddSplitCliffordEquivProdMatrix (K := ℂ) (M := M))).trans
        (AlgEquiv.prodCongr (Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.reindexAlgEquiv ℂ ℂ e))

end

end Spinor
