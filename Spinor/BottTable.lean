import Spinor.Cl78PositiveEven

/-!
  The theorem-facing real Bott table package.

  The concrete low-dimensional files prove each row separately. This module collects the
  already-proved split families and the first-period definite rows into one declaration whose
  type records the formalized table entries.
-/

namespace Spinor
namespace RealClassification

noncomputable section

open scoped Quaternion

local notation "H" => ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]

/-- Full real matrix algebra used in the packaged real Bott table. -/
abbrev MatR (n : ℕ) : Type :=
  Matrix (Fin n) (Fin n) ℝ

/-- Full complex matrix algebra, viewed as a real algebra, used in the packaged real Bott table. -/
abbrev MatC (n : ℕ) : Type :=
  Matrix (Fin n) (Fin n) ℂ

/-- Full Hamilton-quaternion matrix algebra used in the packaged real Bott table. -/
abbrev MatH (n : ℕ) : Type :=
  Matrix (Fin n) (Fin n) H

/-!
## Arbitrary-signature recursive Bott-step interface

The declarations in this section are not a replacement for the first-period matrix table below.
They package the general recursive Clifford-algebra steps that are available for every real
signature: adjoining one negative square identifies a Clifford algebra with an even Clifford
algebra, even Clifford algebras are invariant under sign reversal, and the auxiliary forms
are transported back to the standard signature coordinates.
-/

/-- Canonical arbitrary real signature form for the recursive Bott-step interface. -/
abbrev Q_p_q (p q : ℕ) : QuadraticForm ℝ ((Fin p ⊕ Fin q) → ℝ) :=
  standardSignatureForm p q

/-- The one-negative-square extension used by Mathlib's even-Clifford recursion. -/
abbrev Q_p_q_oneNeg (p q : ℕ) :
    QuadraticForm ℝ (((Fin p ⊕ Fin q) → ℝ) × ℝ) :=
  CliffordAlgebra.EquivEven.Q' (Q_p_q p q)

/-- Append one real coordinate to a finite tuple. -/
def finSnocReal {q : ℕ} (f : Fin q → ℝ) (r : ℝ) : Fin (q + 1) → ℝ :=
  Fin.snoc f r

/-- Coordinate equivalence identifying Mathlib's one-negative-square extension with the
standard signature form having one additional negative square. -/
noncomputable def Q_p_q_oneNegLinearEquiv (p q : ℕ) :
    (((Fin p ⊕ Fin q) → ℝ) × ℝ) ≃ₗ[ℝ] ((Fin p ⊕ Fin (q + 1)) → ℝ) where
  toFun x := fun
    | Sum.inl i => x.1 (Sum.inl i)
    | Sum.inr j => finSnocReal (fun k : Fin q => x.1 (Sum.inr k)) x.2 j
  invFun y :=
    (fun
      | Sum.inl i => y (Sum.inl i)
      | Sum.inr j => y (Sum.inr (Fin.castSucc j)),
      y (Sum.inr (Fin.last q)))
  left_inv x := by
    rcases x with ⟨f, r⟩
    apply Prod.ext
    · funext i
      cases i with
      | inl i => rfl
      | inr j => simp [finSnocReal]
    · simp [finSnocReal]
  right_inv y := by
    funext i
    cases i with
    | inl i => rfl
    | inr j =>
        cases j using Fin.lastCases <;> simp [finSnocReal]
  map_add' x y := by
    funext i
    cases i with
    | inl i => rfl
    | inr j =>
        cases j using Fin.lastCases <;> simp [finSnocReal]
  map_smul' c x := by
    funext i
    cases i with
    | inl i => rfl
    | inr j =>
        cases j using Fin.lastCases <;> simp [finSnocReal]

/-- Mathlib's one-negative-square extension is the standard `(p,q+1)` signature form. -/
noncomputable def Q_p_q_oneNegIsometry (p q : ℕ) :
    (Q_p_q_oneNeg p q).IsometryEquiv (Q_p_q p (q + 1)) where
  toLinearEquiv := Q_p_q_oneNegLinearEquiv p q
  map_app' x := by
    rcases x with ⟨f, r⟩
    have hsnoc :
        (∑ x : Fin (q + 1),
            Fin.snoc (fun k : Fin q => f (Sum.inr k)) r x *
              Fin.snoc (fun k : Fin q => f (Sum.inr k)) r x) =
          (∑ x : Fin q, f (Sum.inr x) * f (Sum.inr x)) + r * r := by
      rw [Fin.sum_univ_castSucc]
      simp
    simp [Q_p_q_oneNeg, Q_p_q, Q_p_q_oneNegLinearEquiv, standardSignatureForm,
      QuadraticMap.weightedSumSquares_apply, finSnocReal, hsnoc, add_comm, add_left_comm]

/-- Coordinate swap identifying the negative of the standard `(p,q)` form with `(q,p)`. -/
noncomputable def Q_p_q_negLinearEquiv (p q : ℕ) :
    ((Fin p ⊕ Fin q) → ℝ) ≃ₗ[ℝ] ((Fin q ⊕ Fin p) → ℝ) where
  toFun f := fun
    | Sum.inl j => f (Sum.inr j)
    | Sum.inr i => f (Sum.inl i)
  invFun f := fun
    | Sum.inl i => f (Sum.inr i)
    | Sum.inr j => f (Sum.inl j)
  left_inv f := by
    funext i
    cases i <;> rfl
  right_inv f := by
    funext i
    cases i <;> rfl
  map_add' f g := by
    funext i
    cases i <;> rfl
  map_smul' c f := by
    funext i
    cases i <;> rfl

/-- Sign reversal for the standard `(p,q)` form is isometric to the standard `(q,p)` form. -/
noncomputable def Q_p_q_negIsometry (p q : ℕ) :
    (-(Q_p_q p q)).IsometryEquiv (Q_p_q q p) where
  toLinearEquiv := Q_p_q_negLinearEquiv p q
  map_app' f := by
    simp [Q_p_q, Q_p_q_negLinearEquiv, standardSignatureForm,
      QuadraticMap.weightedSumSquares_apply, Finset.sum_neg_distrib,
      neg_add_rev, add_comm]

/-- The arbitrary-signature one-negative-step recurrence:
`Cl(p,q) ≃ Cl⁺(Q(p,q) ⊕ ⟨-1⟩)`. -/
noncomputable def cl_p_q_equiv_even_oneNeg (p q : ℕ) :
    CliffordAlgebra (Q_p_q p q) ≃ₐ[ℝ]
      CliffordAlgebra.even (Q_p_q_oneNeg p q) :=
  CliffordAlgebra.equivEven (Q_p_q p q)

/-- The arbitrary-signature even-Clifford sign-reversal recurrence:
`Cl⁺(p,q) ≃ Cl⁺(-Q(p,q))`. -/
noncomputable def cl_p_q_even_equiv_even_neg (p q : ℕ) :
    CliffordAlgebra.even (Q_p_q p q) ≃ₐ[ℝ]
      CliffordAlgebra.even (-(Q_p_q p q)) :=
  CliffordAlgebra.evenEquivEvenNeg (Q := Q_p_q p q)

/-- Standard-coordinate one-negative recurrence:
`Cl(p,q) ≃ Cl⁺(p,q+1)`. -/
noncomputable def cl_p_q_equiv_even_succ_neg (p q : ℕ) :
    CliffordAlgebra (Q_p_q p q) ≃ₐ[ℝ]
      CliffordAlgebra.even (Q_p_q p (q + 1)) :=
  (cl_p_q_equiv_even_oneNeg p q).trans
    (evenCliffordEquivOfIsometry (Q_p_q_oneNegIsometry p q))

/-- Standard-coordinate even-Clifford signature swap:
`Cl⁺(p,q) ≃ Cl⁺(q,p)`. -/
noncomputable def cl_p_q_even_equiv_even_swap (p q : ℕ) :
    CliffordAlgebra.even (Q_p_q p q) ≃ₐ[ℝ]
      CliffordAlgebra.even (Q_p_q q p) :=
  (cl_p_q_even_equiv_even_neg p q).trans
    (evenCliffordEquivOfIsometry (Q_p_q_negIsometry p q))

/-- A theorem-facing package for the arbitrary-signature recursive Clifford steps. -/
structure RecursiveSignatureBottStep where
  cl_p_q_oneNeg :
    (p q : ℕ) → CliffordAlgebra (Q_p_q p q) ≃ₐ[ℝ]
      CliffordAlgebra.even (Q_p_q_oneNeg p q)
  cl_p_q_even_neg :
    (p q : ℕ) → CliffordAlgebra.even (Q_p_q p q) ≃ₐ[ℝ]
      CliffordAlgebra.even (-(Q_p_q p q))
  cl_p_q_succ_neg :
    (p q : ℕ) → CliffordAlgebra (Q_p_q p q) ≃ₐ[ℝ]
      CliffordAlgebra.even (Q_p_q p (q + 1))
  cl_p_q_even_swap :
    (p q : ℕ) → CliffordAlgebra.even (Q_p_q p q) ≃ₐ[ℝ]
      CliffordAlgebra.even (Q_p_q q p)

/-- The collected arbitrary-signature recursive Clifford steps. -/
noncomputable def recursiveSignatureBottStep : RecursiveSignatureBottStep where
  cl_p_q_oneNeg := cl_p_q_equiv_even_oneNeg
  cl_p_q_even_neg := cl_p_q_even_equiv_even_neg
  cl_p_q_succ_neg := cl_p_q_equiv_even_succ_neg
  cl_p_q_even_swap := cl_p_q_even_equiv_even_swap

/--
The formal first-period real Bott table already proved in the component files.

The first three fields record the uniform split rows. The remaining fields record the
canonical definite rows through eight generators, together with their even Clifford
companions. This is intentionally a package of proved algebra equivalences, not a recursive
periodicity theorem for arbitrary signatures.
-/
structure PeriodEightTable where
  cl_n_n :
    (n : ℕ) → CliffordAlgebra (Q_n_n n) ≃ₐ[ℝ] MatR (2 ^ n)
  cl_n_n_even :
    (n : ℕ) → (hn : 0 < n) →
      CliffordAlgebra.even (Q_n_n n) ≃ₐ[ℝ] MatR (2 ^ (n - 1)) × MatR (2 ^ (n - 1))
  cl_succ_n_n :
    (n : ℕ) → CliffordAlgebra (Q_succ_n_n n) ≃ₐ[ℝ] MatR (2 ^ n) × MatR (2 ^ n)
  cl_0_0 :
    CliffordAlgebra Q_0_0 ≃ₐ[ℝ] ℝ
  cl_1_0 :
    CliffordAlgebra Q_1_0 ≃ₐ[ℝ] ℝ × ℝ
  cl_1_0_even :
    CliffordAlgebra.even Q_1_0 ≃ₐ[ℝ] ℝ
  cl_0_1 :
    CliffordAlgebra Q_0_1 ≃ₐ[ℝ] ℂ
  cl_0_1_even :
    CliffordAlgebra.even Q_0_1 ≃ₐ[ℝ] ℝ
  cl_0_2 :
    CliffordAlgebra Q_0_2 ≃ₐ[ℝ] H
  cl_0_2_even :
    CliffordAlgebra.even Q_0_2 ≃ₐ[ℝ] ℂ
  cl_2_0 :
    CliffordAlgebra Q_2_0 ≃ₐ[ℝ] MatR 2
  cl_2_0_even :
    CliffordAlgebra.even Q_2_0 ≃ₐ[ℝ] ℂ
  cl_3_0 :
    CliffordAlgebra Q_3_0 ≃ₐ[ℝ] MatC 2
  cl_3_0_even :
    CliffordAlgebra.even Q_3_0 ≃ₐ[ℝ] H
  cl_0_3 :
    CliffordAlgebra Q_0_3 ≃ₐ[ℝ] H × H
  cl_0_3_even :
    CliffordAlgebra.even Q_0_3 ≃ₐ[ℝ] H
  cl_0_4 :
    CliffordAlgebra Q_0_4 ≃ₐ[ℝ] MatH 2
  cl_0_4_even :
    CliffordAlgebra.even Q_0_4 ≃ₐ[ℝ] H × H
  cl_4_0 :
    CliffordAlgebra Q_4_0 ≃ₐ[ℝ] MatH 2
  cl_4_0_even :
    CliffordAlgebra.even Q_4_0 ≃ₐ[ℝ] H × H
  cl_0_5 :
    CliffordAlgebra Q_0_5 ≃ₐ[ℝ] MatC 4
  cl_0_5_even :
    CliffordAlgebra.even Q_0_5 ≃ₐ[ℝ] MatH 2
  cl_5_0 :
    CliffordAlgebra Q_5_0 ≃ₐ[ℝ] MatH 2 × MatH 2
  cl_5_0_even :
    CliffordAlgebra.even Q_5_0 ≃ₐ[ℝ] MatH 2
  cl_0_6 :
    CliffordAlgebra Q_0_6 ≃ₐ[ℝ] MatR 8
  cl_0_6_even :
    CliffordAlgebra.even Q_0_6 ≃ₐ[ℝ] MatC 4
  cl_6_0 :
    CliffordAlgebra Q_6_0 ≃ₐ[ℝ] MatH 4
  cl_6_0_even :
    CliffordAlgebra.even Q_6_0 ≃ₐ[ℝ] MatC 4
  cl_0_7 :
    CliffordAlgebra Q_0_7 ≃ₐ[ℝ] MatR 8 × MatR 8
  cl_0_7_even :
    CliffordAlgebra.even Q_0_7 ≃ₐ[ℝ] MatR 8
  cl_7_0 :
    CliffordAlgebra Q_7_0 ≃ₐ[ℝ] MatC 8
  cl_7_0_even :
    CliffordAlgebra.even Q_7_0 ≃ₐ[ℝ] MatR 8
  cl_0_8 :
    CliffordAlgebra Q_0_8 ≃ₐ[ℝ] MatR 16
  cl_0_8_even :
    CliffordAlgebra.even Q_0_8 ≃ₐ[ℝ] MatR 8 × MatR 8
  cl_8_0 :
    CliffordAlgebra Q_8_0 ≃ₐ[ℝ] MatR 16
  cl_8_0_even :
    CliffordAlgebra.even Q_8_0 ≃ₐ[ℝ] MatR 8 × MatR 8

/--
The collected first-period real Bott table. Every field is filled by one of the concrete
classification equivalences proved elsewhere in the library.
-/
noncomputable def periodEightTable : PeriodEightTable where
  cl_n_n := cl_n_n_equivMatrix
  cl_n_n_even := cl_n_n_even_equivProdMatrix
  cl_succ_n_n := cl_succ_n_n_equivProdMatrix
  cl_0_0 := cl_0_0_equivReal
  cl_1_0 := cl_1_0_equivRealProd
  cl_1_0_even := cl_1_0_even_equivReal
  cl_0_1 := cl_0_1_equivComplex
  cl_0_1_even := cl_0_1_even_equivReal
  cl_0_2 := cl_0_2_equivQuaternion
  cl_0_2_even := cl_0_2_even_equivComplex
  cl_2_0 := cl_2_0_equivMatrix2
  cl_2_0_even := cl_2_0_even_equivComplex
  cl_3_0 := cl_3_0_equivComplexMatrix2
  cl_3_0_even := cl_3_0_even_equivQuaternion
  cl_0_3 := cl_0_3_equivQuaternionProd
  cl_0_3_even := cl_0_3_even_equivQuaternion
  cl_0_4 := cl_0_4_equivQuaternionMatrix2
  cl_0_4_even := cl_0_4_even_equivQuaternionProd
  cl_4_0 := cl_4_0_equivQuaternionMatrix2
  cl_4_0_even := cl_4_0_even_equivQuaternionProd
  cl_0_5 := cl_0_5_equivComplexMatrix4
  cl_0_5_even := cl_0_5_even_equivQuaternionMatrix2
  cl_5_0 := cl_5_0_equivQuaternionMatrix2Prod
  cl_5_0_even := cl_5_0_even_equivQuaternionMatrix2
  cl_0_6 := cl_0_6_equivMatrix8
  cl_0_6_even := cl_0_6_even_equivComplexMatrix4
  cl_6_0 := cl_6_0_equivQuaternionMatrix4
  cl_6_0_even := cl_6_0_even_equivComplexMatrix4
  cl_0_7 := cl_0_7_equivMatrix8Prod
  cl_0_7_even := cl_0_7_even_equivMatrix8
  cl_7_0 := cl_7_0_equivComplexMatrix8
  cl_7_0_even := cl_7_0_even_equivMatrix8
  cl_0_8 := cl_0_8_equivMatrix16
  cl_0_8_even := cl_0_8_even_equivMatrix8Prod
  cl_8_0 := cl_8_0_equivMatrix16
  cl_8_0_even := cl_8_0_even_equivMatrix8Prod

end

end RealClassification
end Spinor
