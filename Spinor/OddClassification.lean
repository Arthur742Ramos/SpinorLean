/- 
  Odd split Clifford classification via `CliffordAlgebra.equivEven`.

  This packages the standard odd split form `dualProd K M ⊕ ⟨1⟩` by identifying its Clifford
  algebra with the even Clifford algebra of a one-up hyperbolic form, then applying the chosen
  half-spin product classification proved for split even Clifford algebras.
-/

import Spinor.ProdNeg
import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv
import Mathlib.LinearAlgebra.Matrix.Unique

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
      simp [mul_comm]
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
    ext v <;> simp [QuadraticMap.Isometry.comp_apply]
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
    ext v <;> simp [QuadraticMap.Isometry.comp_apply]
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
    have htopEquiv :=
      (LinearEquiv.finrank_eq
        (Submodule.topEquiv : (⊤ : Submodule K (M × K)) ≃ₗ[K] (M × K))).symm
    rw [Module.finrank_prod] at htopEquiv
    calc
      Module.finrank K (⊤ : Submodule K (M × K)) = Module.finrank K M + Module.finrank K K :=
        htopEquiv.symm
      _ = Module.finrank K M + 1 := by simp
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

section DualProdLine

/-- Transport the split line `H(K)` from the ambient module `K` to its top submodule. -/
noncomputable def dualProdLineTopIsometry :
    (QuadraticForm.dualProd K K).IsometryEquiv
      (QuadraticForm.dualProd K (⊤ : Submodule K K)) :=
  QuadraticForm.dualProdIsometry (R := K)
    (Submodule.topEquiv.symm : K ≃ₗ[K] (⊤ : Submodule K K))

/-- Transport the even Clifford algebra of the split line to the top-submodule model. -/
noncomputable def dualProdLineEvenCliffordMap :
    CliffordAlgebra.even (QuadraticForm.dualProd K K) →ₐ[K]
      CliffordAlgebra.even (QuadraticForm.dualProd K (⊤ : Submodule K K)) where
  toFun a := ⟨CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).toIsometry a.1,
    cliffordMap_mem_evenOdd_zero (K := K) (dualProdLineTopIsometry (K := K)) a.2⟩
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

/-- The transported even Clifford map for the split line is surjective. -/
theorem dualProdLineEvenCliffordMap_surjective :
    Function.Surjective (dualProdLineEvenCliffordMap (K := K)) := by
  intro a
  refine ⟨⟨CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).symm.toIsometry a.1,
      cliffordMap_mem_evenOdd_zero (K := K) (dualProdLineTopIsometry (K := K)).symm a.2⟩, ?_⟩
  ext
  have hright :
      (dualProdLineTopIsometry (K := K)).toIsometry.comp
          (dualProdLineTopIsometry (K := K)).symm.toIsometry =
        QuadraticMap.Isometry.id (QuadraticForm.dualProd K (⊤ : Submodule K K)) := by
    ext v <;> simp [QuadraticMap.Isometry.comp_apply]
  have hmap :
      CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).toIsometry
          (CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).symm.toIsometry a.1) =
        CliffordAlgebra.map
          ((dualProdLineTopIsometry (K := K)).toIsometry.comp
            (dualProdLineTopIsometry (K := K)).symm.toIsometry) a.1 := by
    change
      ((CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).toIsometry).comp
          (CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).symm.toIsometry)) a.1 =
        CliffordAlgebra.map
          ((dualProdLineTopIsometry (K := K)).toIsometry.comp
            (dualProdLineTopIsometry (K := K)).symm.toIsometry) a.1
    exact congrArg (fun φ => φ a.1)
      (CliffordAlgebra.map_comp_map
        (f := (dualProdLineTopIsometry (K := K)).toIsometry)
        (g := (dualProdLineTopIsometry (K := K)).symm.toIsometry))
  change
    CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).toIsometry
      (CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).symm.toIsometry a.1) = a.1
  rw [hmap, hright, CliffordAlgebra.map_id]
  rfl

/-- The transported even Clifford map for the split line is injective. -/
theorem dualProdLineEvenCliffordMap_injective :
    Function.Injective (dualProdLineEvenCliffordMap (K := K)) := by
  intro a b h
  apply Subtype.ext
  have hval :
      CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).toIsometry a.1 =
        CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).toIsometry b.1 :=
    congrArg Subtype.val h
  have hback :=
    congrArg (CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).symm.toIsometry) hval
  have hleft :
      (dualProdLineTopIsometry (K := K)).symm.toIsometry.comp
          (dualProdLineTopIsometry (K := K)).toIsometry =
        QuadraticMap.Isometry.id (QuadraticForm.dualProd K K) := by
    ext v <;> simp [dualProdLineTopIsometry, QuadraticMap.Isometry.comp_apply,
      QuadraticForm.dualProdIsometry]
  have hmapa :
      CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).symm.toIsometry
          (CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).toIsometry a.1) =
        CliffordAlgebra.map
          ((dualProdLineTopIsometry (K := K)).symm.toIsometry.comp
            (dualProdLineTopIsometry (K := K)).toIsometry) a.1 := by
    change
      ((CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).symm.toIsometry).comp
          (CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).toIsometry)) a.1 =
        CliffordAlgebra.map
          ((dualProdLineTopIsometry (K := K)).symm.toIsometry.comp
            (dualProdLineTopIsometry (K := K)).toIsometry) a.1
    exact congrArg (fun φ => φ a.1)
      (CliffordAlgebra.map_comp_map
        (f := (dualProdLineTopIsometry (K := K)).symm.toIsometry)
        (g := (dualProdLineTopIsometry (K := K)).toIsometry))
  have hmapb :
      CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).symm.toIsometry
          (CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).toIsometry b.1) =
        CliffordAlgebra.map
          ((dualProdLineTopIsometry (K := K)).symm.toIsometry.comp
            (dualProdLineTopIsometry (K := K)).toIsometry) b.1 := by
    change
      ((CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).symm.toIsometry).comp
          (CliffordAlgebra.map (dualProdLineTopIsometry (K := K)).toIsometry)) b.1 =
        CliffordAlgebra.map
          ((dualProdLineTopIsometry (K := K)).symm.toIsometry.comp
            (dualProdLineTopIsometry (K := K)).toIsometry) b.1
    exact congrArg (fun φ => φ b.1)
      (CliffordAlgebra.map_comp_map
        (f := (dualProdLineTopIsometry (K := K)).symm.toIsometry)
        (g := (dualProdLineTopIsometry (K := K)).toIsometry))
  rw [hmapa, hmapb, hleft, CliffordAlgebra.map_id] at hback
  exact hback

variable [Invertible (2 : K)]

/-- The even and odd halves of `⋀(K)` on the split line are both one-dimensional. -/
theorem finrank_evenOddDualProdLineExterior :
    Module.finrank K (evenExteriorSubmodule (K := K) (⊤ : Submodule K K)) = 1 ∧
      Module.finrank K (oddExteriorSubmodule (K := K) (⊤ : Submodule K K)) = 1 := by
  have hTopFinrank : Module.finrank K (⊤ : Submodule K K) = 1 := by
    rw [LinearEquiv.finrank_eq (Submodule.topEquiv : (⊤ : Submodule K K) ≃ₗ[K] K)]
    simp
  have htop : 0 < Module.finrank K (⊤ : Submodule K K) := by
    rw [hTopFinrank]
    exact Nat.succ_pos 0
  constructor
  · simpa [hTopFinrank] using
      finrank_evenExterior (K := K) (⊤ : Submodule K K) htop
  · simpa [hTopFinrank] using
      finrank_oddExterior (K := K) (⊤ : Submodule K K) htop

/-- The even Clifford algebra of the split line `H(K)` is `K × K`. -/
noncomputable def dualProdLineEvenCliffordEquivProd :
    CliffordAlgebra.even (QuadraticForm.dualProd K K) ≃ₐ[K] K × K := by
  let bTop := Module.finBasis K (⊤ : Submodule K K)
  letI : FiniteDimensional K (IsotropicExteriorModel (K := K) (⊤ : Submodule K K)) :=
    bTop.ExteriorAlgebra.finiteDimensional_of_finite
  let hEven := (finrank_evenOddDualProdLineExterior (K := K)).1
  let hOdd := (finrank_evenOddDualProdLineExterior (K := K)).2
  let bEven :
      Module.Basis (Fin 1) K (evenExteriorSubmodule (K := K) (⊤ : Submodule K K)) :=
    Module.finBasisOfFinrankEq K
      (evenExteriorSubmodule (K := K) (⊤ : Submodule K K)) hEven
  let bOdd :
      Module.Basis (Fin 1) K (oddExteriorSubmodule (K := K) (⊤ : Submodule K K)) :=
    Module.finBasisOfFinrankEq K
      (oddExteriorSubmodule (K := K) (⊤ : Submodule K K)) hOdd
  let e : Fin 1 ≃ Unit := finOneEquiv
  exact
    (AlgEquiv.ofBijective (dualProdLineEvenCliffordMap (K := K))
      ⟨dualProdLineEvenCliffordMap_injective (K := K),
        dualProdLineEvenCliffordMap_surjective (K := K)⟩).trans
      ((evenSplitCliffordEquivProdEnd (K := K) (⊤ : Submodule K K)).trans
        (AlgEquiv.prodCongr
          ((LinearMap.toMatrixAlgEquiv bEven).trans
            ((Matrix.reindexAlgEquiv K K e).trans
              (Matrix.uniqueAlgEquiv (R := K) (A := K) (m := Unit))))
          ((LinearMap.toMatrixAlgEquiv bOdd).trans
            ((Matrix.reindexAlgEquiv K K e).trans
              (Matrix.uniqueAlgEquiv (R := K) (A := K) (m := Unit))))))

end DualProdLine

end Spinor
