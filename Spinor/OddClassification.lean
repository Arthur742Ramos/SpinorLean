/- 
  Odd split Clifford classification via `CliffordAlgebra.equivEven`.

  This packages the standard odd split form `dualProd K M ⊕ ⟨1⟩` by identifying its Clifford
  algebra with the even Clifford algebra of a one-up hyperbolic form, then applying the chosen
  half-spin product classification proved for split even Clifford algebras.
-/

import Spinor.ProdNeg
import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv

/-!
# Odd split Clifford classification

Classification of the standard odd split form `H(M) ⊕ ⟨1⟩` as a product of two matrix
algebras by combining `CliffordAlgebra.equivEven` with the even-Clifford product-endomorphism
classification from `Spinor.Presentation` and `Spinor.ProdNeg`.

More precisely, the one-up hyperbolic form whose even Clifford algebra is `H(M) ⊕ ⟨1⟩` is
identified via Mathlib's `CliffordAlgebra.equivEven` with the `Q ⊕ (-Q)` classification, and
the resulting product-endomorphism equivalence is upgraded to a concrete product-of-matrices
model.

## Main declarations

* `QuadraticMap.IsometryEquiv.prodAssoc` — associativity of `QuadraticForm.prod` as an
  isometry.
* `Spinor.oddSplitForm M` — the quadratic form `H(M) ⊕ ⟨1⟩` on `(Module.Dual K M × M) × K`.
* `Spinor.oddSplitOneUpIsometry` — the isometry identifying `oddSplitForm M` with the even
  Clifford domain of a one-up hyperbolic form.
* `Spinor.oddSplitEvenCliffordMap`, `Spinor.oddSplitEvenCliffordMap_surjective`,
  `Spinor.oddSplitEvenCliffordMap_injective` — the transported Clifford map and its
  bijectivity.
* `Spinor.oddSplitOneUpEvenEquivProdEnd`, `Spinor.oddSplitCliffordEquivProdEnd`,
  `Spinor.oddSplitCliffordEquivProdMatrix` — the product-endomorphism and product-of-matrices
  equivalences classifying `CliffordAlgebra (oddSplitForm M)`.
-/

namespace Spinor

universe uK uM

variable {K : Type uK} [Field K]
variable {M : Type uM} [AddCommGroup M] [Module K M]

open CliffordAlgebra

/-- Associativity of product quadratic forms as an isometry. -/
@[simps!]
def QuadraticMap.IsometryEquiv.prodAssoc
    {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [Module K M₁] [Module K M₂] [Module K M₃]
    (Q₁ : QuadraticForm K M₁) (Q₂ : QuadraticForm K M₂) (Q₃ : QuadraticForm K M₃) :
    ((Q₁.prod Q₂).prod Q₃).IsometryEquiv (Q₁.prod (Q₂.prod Q₃)) where
  toLinearEquiv := LinearEquiv.prodAssoc K M₁ M₂ M₃
  map_app' x := by
    rcases x with ⟨⟨x₁, x₂⟩, x₃⟩
    simp [QuadraticMap.prod_apply, add_assoc]

/-- The standard odd split quadratic form `H(M) ⊕ ⟨1⟩`. -/
abbrev oddSplitForm (M : Type uM) [AddCommGroup M] [Module K M] :
    QuadraticForm K ((Module.Dual K M × M) × K) :=
  (QuadraticForm.dualProd K M).prod (QuadraticMap.sq (R := K))

section OddSplitOneUp

variable [FiniteDimensional K M] [Invertible (2 : K)]

/-- The one-dimensional square form is nondegenerate over a field of characteristic `≠ 2`. -/
theorem sq_nondegenerate :
    (QuadraticMap.sq (R := K) : QuadraticForm K K).Nondegenerate := by
  have hAssoc :
      (QuadraticMap.associated (QuadraticMap.sq (R := K) : QuadraticForm K K)).Nondegenerate := by
    rw [QuadraticMap.associated_sq]
    have hRefl : (LinearMap.mul K K).IsRefl := by
      intro x y
      simp [LinearMap.mul_apply', mul_comm]
    rw [hRefl.nondegenerate_iff_separatingLeft]
    intro x hx
    have h1 := hx 1
    simpa using h1
  exact (QuadraticMap.nondegenerate_associated_iff
    (Q := (QuadraticMap.sq (R := K) : QuadraticForm K K))).mp hAssoc

/-- The one-up quadratic form attached to `H(M) ⊕ ⟨1⟩` is hyperbolic on `M × K`. -/
noncomputable def oddSplitOneUpIsometry :
    (CliffordAlgebra.EquivEven.Q' (oddSplitForm (K := K) M)).IsometryEquiv
      (QuadraticForm.dualProd K (⊤ : Submodule K (M × K))) := by
  let eAssoc :
      (CliffordAlgebra.EquivEven.Q' (oddSplitForm (K := K) M)).IsometryEquiv
        ((QuadraticForm.dualProd K M).prod
          ((QuadraticMap.sq (R := K) : QuadraticForm K K).prod (-QuadraticMap.sq (R := K)))) := by
    simpa [oddSplitForm, CliffordAlgebra.EquivEven.Q'] using
      (QuadraticMap.IsometryEquiv.prodAssoc
        (QuadraticForm.dualProd K M)
        (QuadraticMap.sq (R := K) : QuadraticForm K K)
        (-QuadraticMap.sq (R := K)))
  let eSq :
      ((QuadraticMap.sq (R := K) : QuadraticForm K K).prod (-QuadraticMap.sq (R := K))).IsometryEquiv
        (QuadraticForm.dualProd K K) :=
    QuadraticForm.toDualProdEquiv (K := K) (V := K)
      (QuadraticMap.sq (R := K)) (sq_nondegenerate (K := K))
  let eProd :
      ((QuadraticForm.dualProd K M).prod
        ((QuadraticMap.sq (R := K) : QuadraticForm K K).prod (-QuadraticMap.sq (R := K)))).IsometryEquiv
          ((QuadraticForm.dualProd K M).prod (QuadraticForm.dualProd K K)) :=
    (QuadraticMap.IsometryEquiv.refl (QuadraticForm.dualProd K M)).prod eSq
  let eDual :
      ((QuadraticForm.dualProd K M).prod (QuadraticForm.dualProd K K)).IsometryEquiv
        (QuadraticForm.dualProd K (M × K)) :=
    (QuadraticForm.dualProdProdIsometry (R := K) (M := M) (N := K)).symm
  let eTop :
      (QuadraticForm.dualProd K (M × K)).IsometryEquiv
        (QuadraticForm.dualProd K (⊤ : Submodule K (M × K))) :=
    QuadraticForm.dualProdIsometry (R := K)
      (Submodule.topEquiv.symm : (M × K) ≃ₗ[K] (⊤ : Submodule K (M × K)))
  exact eAssoc.trans (eProd.trans (eDual.trans eTop))

/-- Transport the even Clifford algebra along the odd split one-up isometry. -/
noncomputable def oddSplitEvenCliffordMap :
    CliffordAlgebra.even (CliffordAlgebra.EquivEven.Q' (oddSplitForm (K := K) M)) →ₐ[K]
      CliffordAlgebra.even (QuadraticForm.dualProd K (⊤ : Submodule K (M × K))) where
  toFun a := ⟨CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry a.1,
    cliffordMap_mem_evenOdd_zero (K := K) (oddSplitOneUpIsometry (K := K) (M := M)) a.2⟩
  map_zero' := by
    ext
    simp
  map_add' := by
    intro a b
    ext
    simp [map_add]
  map_one' := by
    ext
    simp
  map_mul' := by
    intro a b
    ext
    simp [map_mul]
  commutes' := by
    intro r
    ext
    simp

omit [FiniteDimensional K M] in
/-- The transported even Clifford map for the odd split one-up form is surjective. -/
theorem oddSplitEvenCliffordMap_surjective :
    Function.Surjective (oddSplitEvenCliffordMap (K := K) (M := M)) := by
  intro a
  refine ⟨⟨CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry a.1,
      cliffordMap_mem_evenOdd_zero (K := K) (oddSplitOneUpIsometry (K := K) (M := M)).symm a.2⟩, ?_⟩
  ext
  have hright :
      (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry.comp
          (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry =
        QuadraticMap.Isometry.id (QuadraticForm.dualProd K (⊤ : Submodule K (M × K))) := by
    ext v <;> simp [QuadraticMap.Isometry.comp_apply, LinearEquiv.apply_symm_apply]
  have hmap :
      CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry
          (CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry a.1) =
        CliffordAlgebra.map
          ((oddSplitOneUpIsometry (K := K) (M := M)).toIsometry.comp
            (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry) a.1 := by
    change
      ((CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry).comp
          (CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry)) a.1 =
        CliffordAlgebra.map
          ((oddSplitOneUpIsometry (K := K) (M := M)).toIsometry.comp
            (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry) a.1
    exact congrArg (fun φ => φ a.1)
      (CliffordAlgebra.map_comp_map
        (f := (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry)
        (g := (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry))
  change
    CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry
      (CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry a.1) = a.1
  rw [hmap, hright, CliffordAlgebra.map_id]
  rfl

omit [FiniteDimensional K M] in
/-- The transported even Clifford map for the odd split one-up form is injective. -/
theorem oddSplitEvenCliffordMap_injective :
    Function.Injective (oddSplitEvenCliffordMap (K := K) (M := M)) := by
  intro a b h
  apply Subtype.ext
  have hval :
      CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry a.1 =
        CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry b.1 :=
    congrArg Subtype.val h
  have hback := congrArg (CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry) hval
  have hleft :
      (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry.comp
          (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry =
        QuadraticMap.Isometry.id (CliffordAlgebra.EquivEven.Q' (oddSplitForm (K := K) M)) := by
    ext v <;> simp [QuadraticMap.Isometry.comp_apply, LinearEquiv.symm_apply_apply]
  have hmapa :
      CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry
          (CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry a.1) =
        CliffordAlgebra.map
          ((oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry.comp
            (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry) a.1 := by
    change
      ((CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry).comp
          (CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry)) a.1 =
        CliffordAlgebra.map
          ((oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry.comp
            (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry) a.1
    exact congrArg (fun φ => φ a.1)
      (CliffordAlgebra.map_comp_map
        (f := (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry)
        (g := (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry))
  have hmapb :
      CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry
          (CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry b.1) =
        CliffordAlgebra.map
          ((oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry.comp
            (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry) b.1 := by
    change
      ((CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry).comp
          (CliffordAlgebra.map (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry)) b.1 =
        CliffordAlgebra.map
          ((oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry.comp
            (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry) b.1
    exact congrArg (fun φ => φ b.1)
      (CliffordAlgebra.map_comp_map
        (f := (oddSplitOneUpIsometry (K := K) (M := M)).symm.toIsometry)
        (g := (oddSplitOneUpIsometry (K := K) (M := M)).toIsometry))
  rw [hmapa, hmapb, hleft, CliffordAlgebra.map_id] at hback
  exact hback

/-- The even Clifford algebra of the one-up odd split form is the product of the two chosen
half-spin endomorphism algebras on `M × K`. -/
noncomputable def oddSplitOneUpEvenEquivProdEnd :
    CliffordAlgebra.even (CliffordAlgebra.EquivEven.Q' (oddSplitForm (K := K) M)) ≃ₐ[K]
      Module.End K (evenExteriorSubmodule (K := K) (⊤ : Submodule K (M × K))) ×
        Module.End K (oddExteriorSubmodule (K := K) (⊤ : Submodule K (M × K))) :=
  (AlgEquiv.ofBijective (oddSplitEvenCliffordMap (K := K) (M := M))
      ⟨oddSplitEvenCliffordMap_injective (K := K) (M := M),
        oddSplitEvenCliffordMap_surjective (K := K) (M := M)⟩).trans
    (evenSplitCliffordEquivProdEnd (K := K) (W := (⊤ : Submodule K (M × K))))

/-- The odd split Clifford algebra `Cl(H(M) ⊕ ⟨1⟩)` is the product of the two half-spin
endomorphism algebras on `M × K`. -/
noncomputable def oddSplitCliffordEquivProdEnd :
    CliffordAlgebra (oddSplitForm (K := K) M) ≃ₐ[K]
      Module.End K (evenExteriorSubmodule (K := K) (⊤ : Submodule K (M × K))) ×
        Module.End K (oddExteriorSubmodule (K := K) (⊤ : Submodule K (M × K))) :=
  (CliffordAlgebra.equivEven (oddSplitForm (K := K) M)).trans
    (oddSplitOneUpEvenEquivProdEnd (K := K) (M := M))

/-- The two chosen half-spin modules for the odd split one-up form have dimension `2 ^ dim(M)`. -/
theorem finrank_evenOddSplitOneUpExterior :
    Module.finrank K (evenExteriorSubmodule (K := K) (⊤ : Submodule K (M × K))) =
      2 ^ Module.finrank K M ∧
    Module.finrank K (oddExteriorSubmodule (K := K) (⊤ : Submodule K (M × K))) =
      2 ^ Module.finrank K M := by
  have hTopFinrank :
      Module.finrank K (⊤ : Submodule K (M × K)) = Module.finrank K M + 1 := by
    simpa [Module.finrank_prod] using
      (LinearEquiv.finrank_eq
        (Submodule.topEquiv : (⊤ : Submodule K (M × K)) ≃ₗ[K] (M × K))).symm
  have htop : 0 < Module.finrank K (⊤ : Submodule K (M × K)) := by
    rw [hTopFinrank]
    exact Nat.succ_pos _
  constructor
  · simpa [hTopFinrank] using
      finrank_evenExterior (K := K) (⊤ : Submodule K (M × K)) htop
  · simpa [hTopFinrank] using
      finrank_oddExterior (K := K) (⊤ : Submodule K (M × K)) htop

/-- Matrix-product form of the odd split Clifford algebra
`Cl(H(M) ⊕ ⟨1⟩) ≃ Mat_(2^dim(M))(K) × Mat_(2^dim(M))(K)`. -/
noncomputable def oddSplitCliffordEquivProdMatrix :
    CliffordAlgebra (oddSplitForm (K := K) M) ≃ₐ[K]
      Matrix (Fin (2 ^ Module.finrank K M)) (Fin (2 ^ Module.finrank K M)) K ×
        Matrix (Fin (2 ^ Module.finrank K M)) (Fin (2 ^ Module.finrank K M)) K := by
  let bTop := Module.finBasis K (⊤ : Submodule K (M × K))
  letI : FiniteDimensional K (IsotropicExteriorModel (K := K) (⊤ : Submodule K (M × K))) :=
    bTop.ExteriorAlgebra.finiteDimensional_of_finite
  let hEven := (finrank_evenOddSplitOneUpExterior (K := K) (M := M)).1
  let hOdd := (finrank_evenOddSplitOneUpExterior (K := K) (M := M)).2
  let bEven :
      Module.Basis (Fin (2 ^ Module.finrank K M)) K
        (evenExteriorSubmodule (K := K) (⊤ : Submodule K (M × K))) :=
    Module.finBasisOfFinrankEq K
      (evenExteriorSubmodule (K := K) (⊤ : Submodule K (M × K))) hEven
  let bOdd :
      Module.Basis (Fin (2 ^ Module.finrank K M)) K
        (oddExteriorSubmodule (K := K) (⊤ : Submodule K (M × K))) :=
    Module.finBasisOfFinrankEq K
      (oddExteriorSubmodule (K := K) (⊤ : Submodule K (M × K))) hOdd
  exact (oddSplitCliffordEquivProdEnd (K := K) (M := M)).trans
    (AlgEquiv.prodCongr (LinearMap.toMatrixAlgEquiv bEven) (LinearMap.toMatrixAlgEquiv bOdd))

end OddSplitOneUp

end Spinor
