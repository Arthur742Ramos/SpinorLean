import Spinor.OddClassification
import Spinor.ProdNeg
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.Matrix.Unique

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
  have hfin := Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin n)
  rw [Fintype.card_fin] at hfin
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
  have hfin := Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin n)
  rw [Fintype.card_fin] at hfin
  have hV : 0 < Module.finrank ℝ (Fin n → ℝ) := by
    rw [hfin]
    exact hn
  let e : Fin (2 ^ (Module.finrank ℝ (Fin n → ℝ) - 1)) ≃ Fin (2 ^ (n - 1)) :=
    Equiv.cast (by rw [hfin])
  exact ((evenCliffordEquivOfIsometry (realSplitIsometry n)).trans
    (evenProdNegCliffordEquivProdMatrix (K := ℝ) (V := Fin n → ℝ)
      (realSumSquares (Fin n)) (realSumSquares_nondegenerate (Fin n)) hV)).trans
    (AlgEquiv.prodCongr (Matrix.reindexAlgEquiv ℝ ℝ e) (Matrix.reindexAlgEquiv ℝ ℝ e))

/-- The standard grouped real odd split-signature `(n+1,n)` quadratic form:
an `(n,n)` split block together with one extra positive square. -/
abbrev realOddSplitPositiveForm (n : ℕ) :
    QuadraticForm ℝ (((Fin n ⊕ Fin n) → ℝ) × ℝ) :=
  (standardSignatureForm n n).prod (QuadraticMap.sq (R := ℝ))

/-- The standard grouped real odd split-signature `(n+1,n)` form is explicitly split. -/
noncomputable def realOddSplitPositiveIsometry (n : ℕ) :
    (realOddSplitPositiveForm n).IsometryEquiv
      (oddSplitForm (K := ℝ) (diagSubmodule (K := ℝ) (V := Fin n → ℝ))) := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  let Q : QuadraticForm ℝ (Fin n → ℝ) := realSumSquares (Fin n)
  let hQ : Q.Nondegenerate := realSumSquares_nondegenerate (Fin n)
  simpa [realOddSplitPositiveForm, oddSplitForm] using
    ((realSplitIsometry n).prod (QuadraticMap.IsometryEquiv.refl _)).trans
      ((prodNegSplitIsometry (K := ℝ) (V := Fin n → ℝ) Q hQ).prod
        (QuadraticMap.IsometryEquiv.refl _))

/-- The standard real odd split-signature `(n+1,n)` Clifford algebra is a product of two full
real matrix algebras. -/
noncomputable def realOddSplitPositiveCliffordEquivProdMatrix (n : ℕ) :
    CliffordAlgebra (realOddSplitPositiveForm n) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ ×
        Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  let M := diagSubmodule (K := ℝ) (V := Fin n → ℝ)
  have hfinM : Module.finrank ℝ M = n := by
    simpa [M, Fintype.card_fin] using
      (finrank_diagSubmodule (K := ℝ) (V := Fin n → ℝ)).trans
        (Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin n))
  let e : Fin (2 ^ Module.finrank ℝ M) ≃ Fin (2 ^ n) :=
    Equiv.cast (by rw [hfinM])
  exact
    ((CliffordAlgebra.equivOfIsometry (realOddSplitPositiveIsometry n)).trans
      (oddSplitCliffordEquivProdMatrix (K := ℝ) (M := M))).trans
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

These entries package the zero-dimensional algebra, the canonical positive
one-square algebra `Cl(1,0) ≃ ℝ × ℝ`, and the standard negative-definite
`Cl(0,n)` Clifford algebras as algebra isomorphisms against their classical
targets, starting the rows `Cl(0,0) ≃ ℝ`, `Cl(1,0) ≃ ℝ × ℝ`,
`Cl(0,1) ≃ ℂ`, `Cl(0,2) ≃ ℍ` of the real classification table that underlies
the Bott-period-8 theorem (ROADMAP §4.1).

They are named inside the dedicated `Spinor.RealClassification` namespace so the
real-classification surface is stable. Downstream files extend the same namespace
with canonical aliases for entries whose proofs require concrete low-dimensional
models from `Spinor.LowDimensional`.
-/

namespace RealClassification

open scoped Quaternion

/-- Canonical zero-dimensional quadratic form for `Cl(0,0)`. -/
abbrev Q_0_0 : QuadraticForm ℝ Unit :=
  0

/-- Canonical real-classification entry: `Cl(0,0) ≃ ℝ`. -/
noncomputable def cl_0_0_equivReal :
    CliffordAlgebra Q_0_0 ≃ₐ[ℝ] ℝ := by
  simpa [Q_0_0] using (CliffordAlgebraRing.equiv (R := ℝ))

/-- Canonical split-signature form for `Cl(n,n)`. -/
abbrev Q_n_n (n : ℕ) : QuadraticForm ℝ ((Fin n ⊕ Fin n) → ℝ) :=
  standardSignatureForm n n

/-- Canonical real-classification split row: `Cl(n,n) ≃ Mat_(2^n)(ℝ)`. -/
noncomputable def cl_n_n_equivMatrix (n : ℕ) :
    CliffordAlgebra (Q_n_n n) ≃ₐ[ℝ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ := by
  simpa [Q_n_n] using realSplitCliffordEquivMatrix n

/-- Canonical even split row:
`Cl⁺(n,n) ≃ Mat_(2^(n-1))(ℝ) × Mat_(2^(n-1))(ℝ)` for `0 < n`. -/
noncomputable def cl_n_n_even_equivProdMatrix (n : ℕ) (hn : 0 < n) :
    CliffordAlgebra.even (Q_n_n n) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ (n - 1))) (Fin (2 ^ (n - 1))) ℝ ×
        Matrix (Fin (2 ^ (n - 1))) (Fin (2 ^ (n - 1))) ℝ := by
  simpa [Q_n_n] using realSplitEvenCliffordEquivProdMatrix n hn

/-- Canonical grouped odd split-signature form for `Cl(n+1,n)`. -/
abbrev Q_succ_n_n (n : ℕ) :
    QuadraticForm ℝ (((Fin n ⊕ Fin n) → ℝ) × ℝ) :=
  realOddSplitPositiveForm n

/-- Canonical grouped odd split row:
`Cl(n+1,n) ≃ Mat_(2^n)(ℝ) × Mat_(2^n)(ℝ)`. -/
noncomputable def cl_succ_n_n_equivProdMatrix (n : ℕ) :
    CliffordAlgebra (Q_succ_n_n n) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ ×
        Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ := by
  simpa [Q_succ_n_n] using realOddSplitPositiveCliffordEquivProdMatrix n

/-- Canonical quadratic form for `Cl(1,0)` — the unit positive square on `ℝ`. -/
abbrev Q_1_0 : QuadraticForm ℝ ℝ :=
  QuadraticMap.sq (R := ℝ)

/-- Canonical real-classification entry: `Cl(1,0) ≃ ℝ × ℝ`. -/
noncomputable def cl_1_0_equivRealProd :
    CliffordAlgebra Q_1_0 ≃ₐ[ℝ] ℝ × ℝ := by
  let e : ℝ ≃ₗ[ℝ] (((Fin 0 ⊕ Fin 0) → ℝ) × ℝ) :=
    { toFun := fun r => (0, r)
      invFun := fun x => x.2
      left_inv := fun r => rfl
      right_inv := fun x => by
        rcases x with ⟨f, r⟩
        have hf : f = 0 := Subsingleton.elim _ _
        simp [hf]
      map_add' := fun x y => by
        ext <;> simp
      map_smul' := fun a x => by
        ext <;> simp }
  let iso : Q_1_0.IsometryEquiv (realOddSplitPositiveForm 0) :=
    { toLinearEquiv := e
      map_app' := fun r => by
        simp [e, Q_1_0, realOddSplitPositiveForm, standardSignatureForm] }
  let hodd :
      CliffordAlgebra (realOddSplitPositiveForm 0) ≃ₐ[ℝ]
        Matrix (Fin 1) (Fin 1) ℝ × Matrix (Fin 1) (Fin 1) ℝ := by
    simpa using realOddSplitPositiveCliffordEquivProdMatrix 0
  let efin : Fin 1 ≃ Unit := finOneEquiv
  let emat : Matrix (Fin 1) (Fin 1) ℝ ≃ₐ[ℝ] ℝ :=
    (Matrix.reindexAlgEquiv ℝ ℝ efin).trans
      (Matrix.uniqueAlgEquiv (R := ℝ) (A := ℝ) (m := Unit))
  exact ((CliffordAlgebra.equivOfIsometry iso).trans hodd).trans
    (AlgEquiv.prodCongr emat emat)

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
Further canonical low-dimensional entries are added to this namespace downstream
in `Spinor.LowDimensional` and `Spinor.Cl03QuaternionProd`, where the concrete
forms and compact-spin models used by those proofs are already available.
-/

end RealClassification

end

end Spinor
