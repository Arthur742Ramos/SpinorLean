/- 
  Odd split Clifford classification via `CliffordAlgebra.equivEven`.

  This packages the standard odd split form `dualProd K M ⊕ ⟨1⟩` by identifying its Clifford
  algebra with the even Clifford algebra of a one-up hyperbolic form, then applying the chosen
  half-spin product classification proved for split even Clifford algebras.  It also contains
  the exact split-line image theorem used by the paper's covering-map discussion.
-/

import Spinor.ProdNeg
import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv
import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# Odd split Clifford classification

Classification of the standard odd split form `H(M) ⊕ ⟨1⟩` as a product of two matrix
algebras by combining `CliffordAlgebra.equivEven` with the even-Clifford product-endomorphism
classification from `Spinor.Presentation` and `Spinor.ProdNeg`.

The file also records the exact rank-one spin image: for the split line, the image of the
finite-dimensional spin-to-special-orthogonal representation is precisely the square-scaling
subgroup.

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
* `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_range_dualProdLine_eq_squareScalingSubgroup`
  — exact split-line image theorem identifying the spin image with the square-scaling subgroup.
* `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_dualProdLine_iff_square_surjective`
  and
  `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_not_surjective_dualProdLine_of_exists_nonsquare_unit`
  — the split-line image theorem sharpened to an iff criterion and a theorem-level nonsquare
  obstruction.
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

private noncomputable def dualProdLineTopCoord : Module.Dual K (⊤ : Submodule K K) :=
  { toFun := fun x => x.1
    map_add' := by simp
    map_smul' := by simp }

private noncomputable def dualProdLineTopPrimal : (⊤ : Submodule K K) := ⟨1, by simp⟩

omit [Invertible (2 : K)] in
private theorem dualProdLineTopIsometry_apply_dual :
    dualProdLineTopIsometry (K := K) ((show Module.Dual K K from LinearMap.id), 0) =
      (dualProdLineTopCoord (K := K), 0) := by
  apply Prod.ext
  · change Submodule.topEquiv.dualMap (LinearMap.id : Module.Dual K K) =
      dualProdLineTopCoord (K := K)
    ext x
    simp [dualProdLineTopCoord, LinearEquiv.dualMap_apply]
  · rfl

omit [Invertible (2 : K)] in
private theorem dualProdLineTopIsometry_apply_primal :
    dualProdLineTopIsometry (K := K) (0, (1 : K)) =
      (0, dualProdLineTopPrimal (K := K)) := by
  apply Prod.ext
  · rfl
  · change Submodule.topEquiv.symm (1 : K) = dualProdLineTopPrimal (K := K)
    rfl

private noncomputable def dualProdLineTopEvenUnit :
    evenExteriorSubmodule (K := K) (⊤ : Submodule K K) := ⟨1, by
  refine (mem_evenExteriorSubmodule_of_mem_exteriorPower (K := K)
    (W := (⊤ : Submodule K K)) (n := 0)
    (x := (1 : IsotropicExteriorModel (K := K) (⊤ : Submodule K K)))) ?_ (by simp)
  change (1 : IsotropicExteriorModel (K := K) (⊤ : Submodule K K)) ∈
    (LinearMap.range (ExteriorAlgebra.ι K : (⊤ : Submodule K K) →ₗ[K]
      IsotropicExteriorModel (K := K) (⊤ : Submodule K K)) ^ 0)
  simp⟩

omit [Invertible (2 : K)] in
private theorem dualProdLineTopEvenUnit_ne :
    dualProdLineTopEvenUnit (K := K) ≠ 0 := by
  intro h
  have h' :
      ((dualProdLineTopEvenUnit (K := K) :
        evenExteriorSubmodule (K := K) (⊤ : Submodule K K)) :
        IsotropicExteriorModel (K := K) (⊤ : Submodule K K)) = 0 :=
    congrArg Subtype.val h
  exact one_ne_zero h'

private noncomputable def dualProdLineTopOddUnit :
    oddExteriorSubmodule (K := K) (⊤ : Submodule K K) :=
  ⟨ExteriorAlgebra.ι K (dualProdLineTopPrimal (K := K)), by
    refine (mem_oddExteriorSubmodule_of_mem_exteriorPower (K := K)
      (W := (⊤ : Submodule K K)) (n := 1)
      (x := ExteriorAlgebra.ι K (dualProdLineTopPrimal (K := K)))) ?_ (by simp)
    change ExteriorAlgebra.ι K (dualProdLineTopPrimal (K := K)) ∈
      (LinearMap.range (ExteriorAlgebra.ι K : (⊤ : Submodule K K) →ₗ[K]
        IsotropicExteriorModel (K := K) (⊤ : Submodule K K)) ^ 1)
    rw [pow_one]
    exact LinearMap.mem_range_self _ _⟩

omit [Invertible (2 : K)] in
private theorem dualProdLineTopOddUnit_ne :
    dualProdLineTopOddUnit (K := K) ≠ 0 := by
  intro h
  have h' :
      ((dualProdLineTopOddUnit (K := K) :
        oddExteriorSubmodule (K := K) (⊤ : Submodule K K)) :
        IsotropicExteriorModel (K := K) (⊤ : Submodule K K)) = 0 :=
    congrArg Subtype.val h
  have hw_ne : dualProdLineTopPrimal (K := K) ≠ 0 := by
    intro hw
    have hval : ((dualProdLineTopPrimal (K := K) : (⊤ : Submodule K K)) : K) = 0 :=
      congrArg Subtype.val hw
    exact one_ne_zero hval
  exact hw_ne
    ((ExteriorAlgebra.ι_eq_zero_iff (R := K) (x := dualProdLineTopPrimal (K := K))).mp h')

private noncomputable def dualProdLineTopDualGenerator :
    CliffordAlgebra (QuadraticForm.dualProd K (⊤ : Submodule K K)) :=
  CliffordAlgebra.ι _ (dualProdLineTopCoord (K := K), 0)

private noncomputable def dualProdLineTopPrimalGenerator :
    CliffordAlgebra (QuadraticForm.dualProd K (⊤ : Submodule K K)) :=
  CliffordAlgebra.ι _ (0, dualProdLineTopPrimal (K := K))

private noncomputable def dualProdLineTopProjectorLeft :
    CliffordAlgebra.even (QuadraticForm.dualProd K (⊤ : Submodule K K)) :=
  ⟨dualProdLineTopDualGenerator (K := K) * dualProdLineTopPrimalGenerator (K := K),
    CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero
      (Q := QuadraticForm.dualProd K (⊤ : Submodule K K))
      (dualProdLineTopCoord (K := K), 0) (0, dualProdLineTopPrimal (K := K))⟩

private theorem dualProdLineTopProjectorLeft_blocks :
    evenSplitCliffordActionProd (K := K) (W := (⊤ : Submodule K K))
      (dualProdLineTopProjectorLeft (K := K)) = (1, 0) := by
  have hEven :
      evenSplitCliffordAction (K := K) (W := (⊤ : Submodule K K))
        (dualProdLineTopProjectorLeft (K := K)) = 1 := by
    let u := evenSplitCliffordAction (K := K) (W := (⊤ : Submodule K K))
      (dualProdLineTopProjectorLeft (K := K))
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
      ((finrank_evenOddDualProdLineExterior (K := K)).1) u
    have hEval : u (dualProdLineTopEvenUnit (K := K)) = c • dualProdLineTopEvenUnit (K := K) := by
      rw [hc]
      simp
    have hone_eval :
        u (dualProdLineTopEvenUnit (K := K)) = dualProdLineTopEvenUnit (K := K) := by
      simpa [u] using (show
        evenSplitCliffordAction (K := K) (W := (⊤ : Submodule K K))
            (dualProdLineTopProjectorLeft (K := K)) (dualProdLineTopEvenUnit (K := K)) =
          dualProdLineTopEvenUnit (K := K) by
        ext
        simp [dualProdLineTopProjectorLeft, dualProdLineTopDualGenerator,
          dualProdLineTopPrimalGenerator, dualProdLineTopEvenUnit, dualProdLineTopPrimal,
          dualProdLineTopCoord, evenSplitCliffordAction, splitCliffordAction_apply_ι,
          splitGeneratorAction, wedgeAction_apply, contractionAction_ι])
    rw [hone_eval] at hEval
    have hc1 : c = 1 := by
      apply smul_left_injective K (dualProdLineTopEvenUnit_ne (K := K))
      simpa [one_smul] using hEval.symm
    simpa [u, hc1] using hc
  have hOdd :
      oddSplitCliffordAction (K := K) (W := (⊤ : Submodule K K))
        (dualProdLineTopProjectorLeft (K := K)) = 0 := by
    let u := oddSplitCliffordAction (K := K) (W := (⊤ : Submodule K K))
      (dualProdLineTopProjectorLeft (K := K))
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
      ((finrank_evenOddDualProdLineExterior (K := K)).2) u
    have hEval : u (dualProdLineTopOddUnit (K := K)) = c • dualProdLineTopOddUnit (K := K) := by
      rw [hc]
      simp
    have hodd_eval : u (dualProdLineTopOddUnit (K := K)) = 0 := by
      simpa [u] using (show
        oddSplitCliffordAction (K := K) (W := (⊤ : Submodule K K))
            (dualProdLineTopProjectorLeft (K := K)) (dualProdLineTopOddUnit (K := K)) = 0 by
        ext
        simp [dualProdLineTopProjectorLeft, dualProdLineTopDualGenerator,
          dualProdLineTopPrimalGenerator, dualProdLineTopOddUnit, dualProdLineTopPrimal,
          dualProdLineTopCoord, oddSplitCliffordAction, splitCliffordAction_apply_ι,
          splitGeneratorAction, wedgeAction_apply])
    rw [hodd_eval] at hEval
    have hc0 : c = 0 := by
      apply smul_left_injective K (dualProdLineTopOddUnit_ne (K := K))
      simpa using hEval.symm
    simpa [u, hc0] using hc
  ext <;> simp [evenSplitCliffordActionProd, hEven, hOdd]

private noncomputable def dualProdLineAmbientDualGenerator :
    CliffordAlgebra (QuadraticForm.dualProd K K) :=
  CliffordAlgebra.ι (QuadraticForm.dualProd K K) ((show Module.Dual K K from LinearMap.id), 0)

private noncomputable def dualProdLineAmbientPrimalGenerator :
    CliffordAlgebra (QuadraticForm.dualProd K K) :=
  CliffordAlgebra.ι (QuadraticForm.dualProd K K) (0, (1 : K))

private noncomputable def dualProdLineAmbientProjectorLeft :
    CliffordAlgebra.even (QuadraticForm.dualProd K K) :=
  ⟨dualProdLineAmbientDualGenerator (K := K) * dualProdLineAmbientPrimalGenerator (K := K),
    CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (Q := QuadraticForm.dualProd K K)
      ((show Module.Dual K K from LinearMap.id), 0) (0, (1 : K))⟩

private theorem dualProdLineEvenCliffordEquivProd_projectorLeft :
    dualProdLineEvenCliffordEquivProd (K := K) (dualProdLineAmbientProjectorLeft (K := K)) =
      (1, 0) := by
  let bTop := Module.finBasis K (⊤ : Submodule K K)
  letI : FiniteDimensional K (IsotropicExteriorModel (K := K) (⊤ : Submodule K K)) :=
    bTop.ExteriorAlgebra.finiteDimensional_of_finite
  unfold dualProdLineEvenCliffordEquivProd
  simp [dualProdLineEvenCliffordMap, dualProdLineAmbientProjectorLeft,
    dualProdLineAmbientDualGenerator, dualProdLineAmbientPrimalGenerator,
    dualProdLineTopIsometry_apply_dual, dualProdLineTopIsometry_apply_primal]
  change Prod.map
      ((⇑Matrix.uniqueAlgEquiv ∘ ⇑(Matrix.reindexAlgEquiv K K finOneEquiv)) ∘
        ⇑(LinearMap.toMatrixAlgEquiv
          (Module.finBasisOfFinrankEq K ↥(evenExteriorSubmodule (⊤ : Submodule K K))
            ((finrank_evenOddDualProdLineExterior (K := K)).1))))
      ((⇑Matrix.uniqueAlgEquiv ∘ ⇑(Matrix.reindexAlgEquiv K K finOneEquiv)) ∘
        ⇑(LinearMap.toMatrixAlgEquiv
          (Module.finBasisOfFinrankEq K ↥(oddExteriorSubmodule (⊤ : Submodule K K))
            ((finrank_evenOddDualProdLineExterior (K := K)).2))))
      ((evenSplitCliffordActionProd (K := K) (W := (⊤ : Submodule K K)))
        (dualProdLineTopProjectorLeft (K := K))) = (1, 0)
  rw [dualProdLineTopProjectorLeft_blocks]
  simp

private noncomputable def dualProdLineAmbientProjectorRight :
    CliffordAlgebra.even (QuadraticForm.dualProd K K) :=
  ⟨dualProdLineAmbientPrimalGenerator (K := K) * dualProdLineAmbientDualGenerator (K := K),
    CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (Q := QuadraticForm.dualProd K K)
      (0, (1 : K)) ((show Module.Dual K K from LinearMap.id), 0)⟩

omit [Invertible (2 : K)] in
private theorem dualProdLineAmbientProjector_sum :
    dualProdLineAmbientProjectorLeft (K := K) + dualProdLineAmbientProjectorRight (K := K) =
      (1 : CliffordAlgebra.even (QuadraticForm.dualProd K K)) := by
  apply Subtype.ext
  change dualProdLineAmbientDualGenerator (K := K) * dualProdLineAmbientPrimalGenerator (K := K) +
      dualProdLineAmbientPrimalGenerator (K := K) * dualProdLineAmbientDualGenerator (K := K) = 1
  unfold dualProdLineAmbientDualGenerator dualProdLineAmbientPrimalGenerator
  rw [CliffordAlgebra.ι_mul_ι_add_swap]
  simpa [dualProdLineAmbientDualGenerator, dualProdLineAmbientPrimalGenerator,
    QuadraticMap.polar, QuadraticForm.dualProd] using
      (show algebraMap K (CliffordAlgebra (QuadraticForm.dualProd K K)) (1 : K) = 1 by simp)

private theorem dualProdLineEvenCliffordEquivProd_projectorRight :
    dualProdLineEvenCliffordEquivProd (K := K) (dualProdLineAmbientProjectorRight (K := K)) =
      (0, 1) := by
  have hsum := congrArg (dualProdLineEvenCliffordEquivProd (K := K))
    (dualProdLineAmbientProjector_sum (K := K))
  have hfst := congrArg Prod.fst hsum
  have hsnd := congrArg Prod.snd hsum
  simp [dualProdLineEvenCliffordEquivProd_projectorLeft] at hfst hsnd
  exact Prod.ext hfst hsnd

private theorem dualProdLineEvenCliffordEquivProd_symm_eq
    (a b : K) :
    (dualProdLineEvenCliffordEquivProd (K := K)).symm (a, b) =
      a • dualProdLineAmbientProjectorLeft (K := K) +
        b • dualProdLineAmbientProjectorRight (K := K) := by
  apply (dualProdLineEvenCliffordEquivProd (K := K)).injective
  simp [dualProdLineEvenCliffordEquivProd_projectorLeft,
    dualProdLineEvenCliffordEquivProd_projectorRight, add_comm]

private theorem dualProdLineEvenCliffordEquivProd_decompose
    (x : CliffordAlgebra.even (QuadraticForm.dualProd K K)) :
    x = (dualProdLineEvenCliffordEquivProd (K := K) x).1 •
          dualProdLineAmbientProjectorLeft (K := K) +
        (dualProdLineEvenCliffordEquivProd (K := K) x).2 •
          dualProdLineAmbientProjectorRight (K := K) := by
  simpa using
    (dualProdLineEvenCliffordEquivProd_symm_eq (K := K)
      (dualProdLineEvenCliffordEquivProd (K := K) x).1
      (dualProdLineEvenCliffordEquivProd (K := K) x).2)

omit [Invertible (2 : K)] in
private theorem dualProdLineAmbientPrimal_sq_zero :
    dualProdLineAmbientPrimalGenerator (K := K) * dualProdLineAmbientPrimalGenerator (K := K) = 0 := by
  rw [dualProdLineAmbientPrimalGenerator, CliffordAlgebra.ι_sq_scalar]
  simpa [QuadraticForm.dualProd] using
    (show algebraMap K (CliffordAlgebra (QuadraticForm.dualProd K K)) (0 : K) = 0 by simp)

omit [Invertible (2 : K)] in
private theorem dualProdLineAmbientPrimal_mul_dual :
    dualProdLineAmbientPrimalGenerator (K := K) * dualProdLineAmbientDualGenerator (K := K) =
      1 - dualProdLineAmbientDualGenerator (K := K) * dualProdLineAmbientPrimalGenerator (K := K) := by
  exact eq_sub_of_add_eq (by
    simpa [add_comm] using congrArg Subtype.val (dualProdLineAmbientProjector_sum (K := K)))

omit [Invertible (2 : K)] in
private theorem dualProdLineAmbientProjectorLeft_mul_primal_zero :
    (dualProdLineAmbientProjectorLeft (K := K) :
        CliffordAlgebra (QuadraticForm.dualProd K K)) *
      dualProdLineAmbientPrimalGenerator (K := K) = 0 := by
  rw [dualProdLineAmbientProjectorLeft, mul_assoc, dualProdLineAmbientPrimal_sq_zero, mul_zero]

omit [Invertible (2 : K)] in
private theorem dualProdLineAmbientProjectorRight_mul_primal_eq_primal :
    (dualProdLineAmbientProjectorRight (K := K) :
        CliffordAlgebra (QuadraticForm.dualProd K K)) *
      dualProdLineAmbientPrimalGenerator (K := K) =
      dualProdLineAmbientPrimalGenerator (K := K) := by
  calc
    (dualProdLineAmbientProjectorRight (K := K) :
        CliffordAlgebra (QuadraticForm.dualProd K K)) *
        dualProdLineAmbientPrimalGenerator (K := K) =
      (dualProdLineAmbientPrimalGenerator (K := K) *
          dualProdLineAmbientDualGenerator (K := K)) *
        dualProdLineAmbientPrimalGenerator (K := K) := by
          rfl
    _ =
      (1 - dualProdLineAmbientDualGenerator (K := K) *
          dualProdLineAmbientPrimalGenerator (K := K)) *
        dualProdLineAmbientPrimalGenerator (K := K) := by
          rw [dualProdLineAmbientPrimal_mul_dual]
    _ = dualProdLineAmbientPrimalGenerator (K := K) := by
          rw [sub_mul, one_mul, mul_assoc, dualProdLineAmbientPrimal_sq_zero, mul_zero, sub_zero]

omit [Invertible (2 : K)] in
private theorem dualProdLineAmbientPrimal_mul_projectorRight_zero :
    dualProdLineAmbientPrimalGenerator (K := K) *
      (dualProdLineAmbientProjectorRight (K := K) :
        CliffordAlgebra (QuadraticForm.dualProd K K)) = 0 := by
  rw [dualProdLineAmbientProjectorRight, ← mul_assoc,
    dualProdLineAmbientPrimal_sq_zero, zero_mul]

omit [Invertible (2 : K)] in
private theorem dualProdLineAmbientPrimal_mul_projectorLeft_eq_primal :
    dualProdLineAmbientPrimalGenerator (K := K) *
      (dualProdLineAmbientProjectorLeft (K := K) :
        CliffordAlgebra (QuadraticForm.dualProd K K)) =
      dualProdLineAmbientPrimalGenerator (K := K) := by
  calc
    dualProdLineAmbientPrimalGenerator (K := K) *
        (dualProdLineAmbientProjectorLeft (K := K) :
          CliffordAlgebra (QuadraticForm.dualProd K K)) =
      dualProdLineAmbientPrimalGenerator (K := K) *
        (dualProdLineAmbientDualGenerator (K := K) *
          dualProdLineAmbientPrimalGenerator (K := K)) := by
          rfl
    _ =
      (dualProdLineAmbientPrimalGenerator (K := K) *
          dualProdLineAmbientDualGenerator (K := K)) *
        dualProdLineAmbientPrimalGenerator (K := K) := by
          rw [mul_assoc]
    _ =
      (1 - dualProdLineAmbientDualGenerator (K := K) *
          dualProdLineAmbientPrimalGenerator (K := K)) *
        dualProdLineAmbientPrimalGenerator (K := K) := by
          rw [dualProdLineAmbientPrimal_mul_dual]
    _ = dualProdLineAmbientPrimalGenerator (K := K) := by
          rw [sub_mul, one_mul, mul_assoc, dualProdLineAmbientPrimal_sq_zero, mul_zero, sub_zero]

omit [Invertible (2 : K)] in
private theorem dualProdLineAmbientProjectorLeft_star :
    star ((dualProdLineAmbientProjectorLeft (K := K) :
      CliffordAlgebra.even (QuadraticForm.dualProd K K)) :
        CliffordAlgebra (QuadraticForm.dualProd K K)) =
      dualProdLineAmbientProjectorRight (K := K) := by
  simp [dualProdLineAmbientProjectorLeft, dualProdLineAmbientProjectorRight,
    dualProdLineAmbientDualGenerator, dualProdLineAmbientPrimalGenerator,
    CliffordAlgebra.star_ι]

omit [Invertible (2 : K)] in
private theorem dualProdLineAmbientProjectorRight_star :
    star ((dualProdLineAmbientProjectorRight (K := K) :
      CliffordAlgebra.even (QuadraticForm.dualProd K K)) :
        CliffordAlgebra (QuadraticForm.dualProd K K)) =
      dualProdLineAmbientProjectorLeft (K := K) := by
  simp [dualProdLineAmbientProjectorLeft, dualProdLineAmbientProjectorRight,
    dualProdLineAmbientDualGenerator, dualProdLineAmbientPrimalGenerator,
    CliffordAlgebra.star_ι]

omit [Invertible (2 : K)] in
private theorem dualProdLineStar_mem_even
    {x : CliffordAlgebra (QuadraticForm.dualProd K K)}
    (hx : x ∈ CliffordAlgebra.evenOdd (QuadraticForm.dualProd K K) 0) :
    star x ∈ CliffordAlgebra.evenOdd (QuadraticForm.dualProd K K) 0 := by
  simpa [star_def] using
    ((CliffordAlgebra.reverse_mem_evenOdd_iff (Q := QuadraticForm.dualProd K K)).2
      ((CliffordAlgebra.involute_mem_evenOdd_iff (Q := QuadraticForm.dualProd K K)).2 hx))

/-- The split-line ambient spin image is exactly the square-scaling subgroup. -/
theorem spinSpecialOrthogonalRepresentationFiniteDimensional_range_dualProdLine_eq_squareScalingSubgroup :
    MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional (Q := QuadraticForm.dualProd K K)) =
      dualProdLineSquareScalingSubgroup (K := K) := by
  have hsubset :
      MonoidHom.range
          (spinSpecialOrthogonalRepresentationFiniteDimensional (Q := QuadraticForm.dualProd K K)) ≤
        dualProdLineSquareScalingSubgroup (K := K) := by
    rintro g ⟨x, rfl⟩
    let xe : CliffordAlgebra.even (QuadraticForm.dualProd K K) :=
      ⟨(x : CliffordAlgebra (QuadraticForm.dualProd K K)), spinGroup.mem_even x.prop⟩
    let a := (dualProdLineEvenCliffordEquivProd (K := K) xe).1
    let b := (dualProdLineEvenCliffordEquivProd (K := K) xe).2
    let starxe : CliffordAlgebra.even (QuadraticForm.dualProd K K) :=
      ⟨star ((xe : CliffordAlgebra (QuadraticForm.dualProd K K))),
        dualProdLineStar_mem_even (K := K) xe.2⟩
    have hstar_eq :
        starxe = (dualProdLineEvenCliffordEquivProd (K := K)).symm (b, a) := by
      apply Subtype.ext
      rw [dualProdLineEvenCliffordEquivProd_symm_eq]
      have hxe_val' := congrArg star
        (congrArg Subtype.val (dualProdLineEvenCliffordEquivProd_decompose (K := K) xe))
      calc
        star (xe : CliffordAlgebra (QuadraticForm.dualProd K K)) =
            star
              (a • ((dualProdLineAmbientProjectorLeft (K := K) :
                CliffordAlgebra.even (QuadraticForm.dualProd K K)) :
                  CliffordAlgebra (QuadraticForm.dualProd K K)) +
                b • ((dualProdLineAmbientProjectorRight (K := K) :
                  CliffordAlgebra.even (QuadraticForm.dualProd K K)) :
                    CliffordAlgebra (QuadraticForm.dualProd K K))) := hxe_val'
        _ =
            ((a • dualProdLineAmbientProjectorRight (K := K) +
              b • dualProdLineAmbientProjectorLeft (K := K) :
                CliffordAlgebra.even (QuadraticForm.dualProd K K)) :
              CliffordAlgebra (QuadraticForm.dualProd K K)) := by
              simp [dualProdLineAmbientProjectorLeft_star,
                dualProdLineAmbientProjectorRight_star]
        _ =
            (b • ((dualProdLineAmbientProjectorLeft (K := K) :
              CliffordAlgebra.even (QuadraticForm.dualProd K K)) :
                CliffordAlgebra (QuadraticForm.dualProd K K)) +
            a • ((dualProdLineAmbientProjectorRight (K := K) :
              CliffordAlgebra.even (QuadraticForm.dualProd K K)) :
                CliffordAlgebra (QuadraticForm.dualProd K K))) := by
              simp [add_comm]
    have hstar :
        dualProdLineEvenCliffordEquivProd (K := K) starxe = (b, a) := by
      rw [hstar_eq]
      simp
    have hunit :
        (b, a) * (a, b) = (1 : K × K) := by
      have hxeq : starxe * xe = (1 : CliffordAlgebra.even (QuadraticForm.dualProd K K)) := by
        apply Subtype.ext
        simpa [xe, starxe] using spinGroup.coe_star_mul_self (Q := QuadraticForm.dualProd K K) x
      calc
        (b, a) * (a, b) =
            dualProdLineEvenCliffordEquivProd (K := K) (starxe * xe) := by
              rw [map_mul, hstar]
        _ = 1 := by simpa [hxeq]
    have hab : a * b = 1 := by
      exact congrArg Prod.snd hunit
    have hb_ne : b ≠ 0 := by
      intro hb
      have : (0 : K) = 1 := by simpa [hb] using hab
      exact zero_ne_one this
    have hxe_val :
        (xe : CliffordAlgebra (QuadraticForm.dualProd K K)) =
          a • ((dualProdLineAmbientProjectorLeft (K := K) :
            CliffordAlgebra.even (QuadraticForm.dualProd K K)) :
              CliffordAlgebra (QuadraticForm.dualProd K K)) +
          b • ((dualProdLineAmbientProjectorRight (K := K) :
            CliffordAlgebra.even (QuadraticForm.dualProd K K)) :
              CliffordAlgebra (QuadraticForm.dualProd K K)) := by
      exact congrArg Subtype.val (dualProdLineEvenCliffordEquivProd_decompose (K := K) xe)
    have hxq :
        (xe : CliffordAlgebra (QuadraticForm.dualProd K K)) *
            dualProdLineAmbientPrimalGenerator (K := K) =
          b • dualProdLineAmbientPrimalGenerator (K := K) := by
      rw [hxe_val, add_mul, smul_mul_assoc, smul_mul_assoc,
        dualProdLineAmbientProjectorLeft_mul_primal_zero,
        dualProdLineAmbientProjectorRight_mul_primal_eq_primal]
      simp
    have hstarxe_symm :
        starxe = (dualProdLineEvenCliffordEquivProd (K := K)).symm (b, a) := by
      exact hstar_eq
    have hstarxe_val :
        (starxe : CliffordAlgebra (QuadraticForm.dualProd K K)) =
          b • ((dualProdLineAmbientProjectorLeft (K := K) :
            CliffordAlgebra.even (QuadraticForm.dualProd K K)) :
              CliffordAlgebra (QuadraticForm.dualProd K K)) +
          a • ((dualProdLineAmbientProjectorRight (K := K) :
            CliffordAlgebra.even (QuadraticForm.dualProd K K)) :
              CliffordAlgebra (QuadraticForm.dualProd K K)) := by
      have hstarxe_even :
          starxe =
            b • dualProdLineAmbientProjectorLeft (K := K) +
            a • dualProdLineAmbientProjectorRight (K := K) := by
        rw [hstarxe_symm, dualProdLineEvenCliffordEquivProd_symm_eq]
      exact congrArg Subtype.val hstarxe_even
    have hqstar :
        dualProdLineAmbientPrimalGenerator (K := K) *
            star (xe : CliffordAlgebra (QuadraticForm.dualProd K K)) =
          b • dualProdLineAmbientPrimalGenerator (K := K) := by
      calc
        dualProdLineAmbientPrimalGenerator (K := K) *
            star (xe : CliffordAlgebra (QuadraticForm.dualProd K K)) =
          dualProdLineAmbientPrimalGenerator (K := K) *
            (starxe : CliffordAlgebra (QuadraticForm.dualProd K K)) := by
              rfl
        _ = dualProdLineAmbientPrimalGenerator (K := K) *
              (b • ((dualProdLineAmbientProjectorLeft (K := K) :
                CliffordAlgebra.even (QuadraticForm.dualProd K K)) :
                  CliffordAlgebra (QuadraticForm.dualProd K K)) +
                a • ((dualProdLineAmbientProjectorRight (K := K) :
                  CliffordAlgebra.even (QuadraticForm.dualProd K K)) :
                    CliffordAlgebra (QuadraticForm.dualProd K K))) := by
                rw [hstarxe_val]
        _ = b • dualProdLineAmbientPrimalGenerator (K := K) := by
              rw [mul_add, mul_smul_comm, mul_smul_comm,
                dualProdLineAmbientPrimal_mul_projectorLeft_eq_primal,
                dualProdLineAmbientPrimal_mul_projectorRight_zero]
              simp
    have hprimal :
        (spinSpecialOrthogonalRepresentationFiniteDimensional (Q := QuadraticForm.dualProd K K) x).1
            (0, (1 : K)) =
          (0, b ^ 2) := by
      have hxq' :
          (x : CliffordAlgebra (QuadraticForm.dualProd K K)) *
              dualProdLineAmbientPrimalGenerator (K := K) =
            b • dualProdLineAmbientPrimalGenerator (K := K) := by
        simpa [xe] using hxq
      have hqstar' :
          dualProdLineAmbientPrimalGenerator (K := K) * star x =
            b • dualProdLineAmbientPrimalGenerator (K := K) := by
        simpa [xe] using hqstar
      apply cliffordIota_injective (Q := QuadraticForm.dualProd K K)
      rw [coe_spinSpecialOrthogonalRepresentationFiniteDimensional (Q := QuadraticForm.dualProd K K),
        spinIsometryRepresentation_apply, spinIsometryEquiv_apply, spinLinearRepresentation_apply,
        spinLinearEquiv_ι]
      calc
        ConjAct.toConjAct (spinGroup.toUnits x) • dualProdLineAmbientPrimalGenerator (K := K) =
            (x : CliffordAlgebra (QuadraticForm.dualProd K K)) *
              dualProdLineAmbientPrimalGenerator (K := K) * star x := by
                simp [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct, spinGroup.star_eq_inv,
                  mul_assoc]
        _ = (b • dualProdLineAmbientPrimalGenerator (K := K)) * star x := by
              rw [hxq']
        _ = b • (dualProdLineAmbientPrimalGenerator (K := K) * star x) := by
              rw [smul_mul_assoc]
        _ = b • (b • dualProdLineAmbientPrimalGenerator (K := K)) := by
              rw [hqstar']
        _ = (b ^ 2) • dualProdLineAmbientPrimalGenerator (K := K) := by
              simp [pow_two, smul_smul]
        _ = CliffordAlgebra.ι (QuadraticForm.dualProd K K) (0, b ^ 2) := by
              symm
              rw [dualProdLineAmbientPrimalGenerator, ← map_smul]
              congr
              · apply LinearMap.ext
                intro y
                simp [pow_two]
              · simp [pow_two]
    let g := spinSpecialOrthogonalRepresentationFiniteDimensional (Q := QuadraticForm.dualProd K K) x
    obtain ⟨t, ht⟩ := dualProdLineScalingHom_surjective (K := K) g
    let u : Kˣ := Units.mk0 b hb_ne
    have ht_val : (t : K) = (u ^ 2 : Kˣ) := by
      have h_eval := congrArg (fun h : (QuadraticForm.dualProd K K).specialOrthogonalGroup =>
          Prod.snd (h.1 (0, (1 : K)))) ht
      have hprimal_g : g.1 (0, (1 : K)) = (0, b ^ 2) := by
        simpa [g] using hprimal
      have h_eval' :
          Prod.snd ((dualProdLineScalingHom (K := K) t).1 (0, (1 : K))) = b ^ 2 := by
        simpa [hprimal_g] using h_eval
      change Prod.snd ((dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := K)
        (LinearEquiv.smulOfUnit t)).1 (0, (1 : K))) = b ^ 2 at h_eval'
      rw [dualProdSpecialOrthogonalOfLinearEquiv_apply_smulOfUnit
        (K := K) (a := t) (d := (0 : Module.Dual K K)) (u := (1 : K))] at h_eval'
      simpa [u, pow_two] using h_eval'
    have ht_eq : t = u ^ 2 := Units.ext ht_val
    exact ⟨u, by
      simpa [dualProdLineSquareScalingSubgroup, MonoidHom.comp_apply, ht_eq] using ht⟩
  refine le_antisymm hsubset ?_
  rw [← spinSpecialOrthogonalPairGeneratorSet_dualProdLine_closure_eq_squareScalingSubgroup (K := K)]
  rw [Subgroup.closure_le]
  exact spinSpecialOrthogonalPairGeneratorSet_subset_range (Q := QuadraticForm.dualProd K K)

/-- On the split hyperbolic line, the ambient spin map is surjective exactly over fields whose
unit group is square-surjective. -/
theorem spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_dualProdLine_iff_square_surjective :
    Function.Surjective (spinSpecialOrthogonalRepresentationFiniteDimensional
      (Q := QuadraticForm.dualProd K K)) ↔
      Function.Surjective (powMonoidHom (α := Kˣ) 2) := by
  constructor
  · intro hspin u
    have hmemRange :
        dualProdLineScalingHom (K := K) u ∈
          MonoidHom.range
            (spinSpecialOrthogonalRepresentationFiniteDimensional
              (Q := QuadraticForm.dualProd K K)) := by
      exact hspin (dualProdLineScalingHom (K := K) u)
    have hmemSquare :
        dualProdLineScalingHom (K := K) u ∈ dualProdLineSquareScalingSubgroup (K := K) := by
      simpa [spinSpecialOrthogonalRepresentationFiniteDimensional_range_dualProdLine_eq_squareScalingSubgroup
        (K := K)] using hmemRange
    rcases hmemSquare with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    exact dualProdLineScalingHom_injective (K := K) ht
  · intro hsq
    exact spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_dualProdLine_of_square_surjective
      (K := K) hsq

/-- Consequently, over any field with a nonsquare unit, the ambient split-line spin map is not
surjective onto `SO(1,1)`. -/
theorem spinSpecialOrthogonalRepresentationFiniteDimensional_not_surjective_dualProdLine_of_exists_nonsquare_unit
    (hnsq : ∃ u : Kˣ, u ∉ MonoidHom.range (powMonoidHom (α := Kˣ) 2)) :
    ¬ Function.Surjective (spinSpecialOrthogonalRepresentationFiniteDimensional
      (Q := QuadraticForm.dualProd K K)) := by
  intro hspin
  rcases hnsq with ⟨u, hu⟩
  exact hu
    ((spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_dualProdLine_iff_square_surjective
      (K := K)).1 hspin u)

end DualProdLine

end Spinor
