/- 
  Canonical split presentation for doubled quadratic spaces `Q ⊕ (-Q)`.

  Mathlib already provides the forward isometry `QuadraticForm.toDualProd`. In the nondegenerate
  finite-dimensional case, this file upgrades it to an isometry equivalence and uses it to
  package the chosen `⋀W` spinor model on the diagonal isotropic subspace of `V × V`.
-/

import Spinor.Presentation

namespace QuadraticForm

universe uK uV

variable {K : Type uK} [Field K]
variable {V : Type uV} [AddCommGroup V] [Module K V]

section ToDualProdInjective

variable [Invertible (2 : K)]

/-- For a nondegenerate quadratic form, `toDualProd` is injective. -/
theorem toDualProd_injective (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.Injective (QuadraticForm.toDualProd Q) := by
  have hzero :
      ∀ {x y : V}, (QuadraticForm.toDualProd Q).toLinearMap (x, y) = 0 → x = 0 ∧ y = 0 := by
    intro x y hz
    have hxy : x - y = 0 := by
      simpa [QuadraticForm.toDualProd] using congrArg Prod.snd hz
    have hy : y = x := by simpa using (sub_eq_zero.mp hxy).symm
    subst y
    have hassoc2 : (2 : K) • Q.associated x = 0 := by
      simpa [QuadraticForm.toDualProd, two_smul] using congrArg Prod.fst hz
    have hassoc : Q.associated x = 0 :=
      (isUnit_of_invertible (2 : K)).smul_eq_zero.mp hassoc2
    have hassoc_injective : Function.Injective Q.associated := by
      apply LinearMap.ker_eq_bot.mp
      rw [← QuadraticMap.radical_eq_ker_associated, hQ.radical_eq_bot]
    have hx : x = 0 := hassoc_injective (by simpa using hassoc)
    exact ⟨hx, hx⟩
  intro z w hzw
  rcases z with ⟨x₁, x₂⟩
  rcases w with ⟨y₁, y₂⟩
  have hz :
      (QuadraticForm.toDualProd Q).toLinearMap ((x₁, x₂) - (y₁, y₂)) = 0 := by
    rw [map_sub]
    simpa using sub_eq_zero.mpr hzw
  have hzero' := hzero hz
  ext
  · exact sub_eq_zero.mp hzero'.1
  · exact sub_eq_zero.mp hzero'.2

end ToDualProdInjective

section ToDualProdEquiv

variable [FiniteDimensional K V] [Invertible (2 : K)]

/-- In finite dimension, a nondegenerate doubled quadratic space is canonically hyperbolic. -/
noncomputable def toDualProdEquiv (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (Q.prod <| -Q).IsometryEquiv (QuadraticForm.dualProd K V) where
  toLinearEquiv :=
    LinearEquiv.ofInjectiveOfFinrankEq (QuadraticForm.toDualProd Q).toLinearMap
      (toDualProd_injective (K := K) (V := V) Q hQ) <| by
        have hdual : Module.finrank K (Module.Dual K V) = Module.finrank K V := by
          classical exact LinearEquiv.finrank_eq (Module.Basis.ofVectorSpace K V).toDualEquiv.symm
        rw [Module.finrank_prod, Module.finrank_prod, hdual]
  map_app' x := by
    simpa [LinearEquiv.coe_ofInjectiveOfFinrankEq] using (QuadraticForm.toDualProd Q).map_app' x

end ToDualProdEquiv

end QuadraticForm

namespace Spinor

universe uK uV

variable {K : Type uK} [Field K]
variable {V : Type uV} [AddCommGroup V] [Module K V]

section DiagonalModel

/-- The diagonal embedding `V → V × V`. -/
def diagLinearMap : V →ₗ[K] V × V :=
  LinearMap.prod LinearMap.id LinearMap.id

/-- The diagonal subspace of `V × V`. -/
def diagSubmodule : Submodule K (V × V) :=
  LinearMap.range (diagLinearMap (K := K) (V := V))

/-- The diagonal embedding is injective. -/
theorem diagLinearMap_injective : Function.Injective (diagLinearMap (K := K) (V := V)) := by
  intro x y hxy
  simpa [diagLinearMap] using congrArg Prod.fst hxy

/-- `V` is linearly equivalent to the diagonal subspace of `V × V`. -/
noncomputable def diagLinearEquiv : V ≃ₗ[K] diagSubmodule (K := K) (V := V) :=
  LinearEquiv.ofInjective (diagLinearMap (K := K) (V := V))
    (diagLinearMap_injective (K := K) (V := V))

/-- The diagonal subspace has the same dimension as `V`. -/
theorem finrank_diagSubmodule [FiniteDimensional K V] :
    Module.finrank K (diagSubmodule (K := K) (V := V)) = Module.finrank K V := by
  simpa using (LinearEquiv.finrank_eq (diagLinearEquiv (K := K) (V := V))).symm

/-- The diagonal subspace is totally isotropic for the doubled form `Q ⊕ (-Q)`. -/
theorem diagSubmodule_isTotallyIsotropic (Q : QuadraticForm K V) :
    QuadraticForm.IsTotallyIsotropic ((Q.prod <| -Q) : QuadraticForm K (V × V))
      (diagSubmodule (K := K) (V := V)) := by
  intro x
  rcases x.property with ⟨v, hv⟩
  rw [← hv]
  simp [diagLinearMap]

end DiagonalModel

/-- The chosen `⋀W` spinor model for the doubled quadratic space `Q ⊕ (-Q)`. -/
abbrev prodNegSpinorModule :=
  IsotropicExteriorModel (K := K) (diagSubmodule (K := K) (V := V))

/-- The even half of the doubled chosen spinor model. -/
noncomputable abbrev evenProdNegSpinorModule :=
  evenExteriorSubmodule (K := K) (diagSubmodule (K := K) (V := V))

/-- The odd half of the doubled chosen spinor model. -/
noncomputable abbrev oddProdNegSpinorModule :=
  oddExteriorSubmodule (K := K) (diagSubmodule (K := K) (V := V))

section ProdNegDimensions

variable [FiniteDimensional K V]

/-- The doubled chosen spinor model has dimension `2 ^ dim(V)`. -/
theorem finrank_prodNegSpinorModule :
    Module.finrank K (prodNegSpinorModule (K := K) (V := V)) = 2 ^ Module.finrank K V := by
  rw [finrank_isotropicExteriorModel, finrank_diagSubmodule]

end ProdNegDimensions

section ProdNegTransport

variable [FiniteDimensional K V] [Invertible (2 : K)]

/-- The canonical hyperbolic presentation of `Q ⊕ (-Q)` on the diagonal isotropic subspace. -/
noncomputable def prodNegSplitIsometry (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (Q.prod <| -Q).IsometryEquiv
      (QuadraticForm.dualProd K (diagSubmodule (K := K) (V := V))) :=
  (QuadraticForm.toDualProdEquiv (K := K) (V := V) Q hQ).trans
    (QuadraticForm.dualProdIsometry (R := K) (diagLinearEquiv (K := K) (V := V)))

/-- The canonical explicit hyperbolic presentation of the doubled form `Q ⊕ (-Q)`. -/
noncomputable def prodNegPresentation (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    HyperbolicPresentation (((Q.prod <| -Q) : QuadraticForm K (V × V))) where
  W := diagSubmodule (K := K) (V := V)
  iso := prodNegSplitIsometry (K := K) (V := V) Q hQ

/-- The canonical chosen-model Clifford action for `Q ⊕ (-Q)`. -/
noncomputable def prodNegCliffordAction (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    CliffordAlgebra (Q.prod <| -Q) →ₐ[K] Module.End K (prodNegSpinorModule (K := K) (V := V)) :=
  HyperbolicPresentation.cliffordAction
    (K := K) (Q := ((Q.prod <| -Q) : QuadraticForm K (V × V)))
    (prodNegPresentation (K := K) (V := V) Q hQ)

/-- The canonical module structure on the doubled chosen model. -/
noncomputable abbrev prodNegCliffordModule (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Module (CliffordAlgebra (Q.prod <| -Q)) (prodNegSpinorModule (K := K) (V := V)) :=
  HyperbolicPresentation.cliffordModule
    (K := K) (Q := ((Q.prod <| -Q) : QuadraticForm K (V × V)))
    (prodNegPresentation (K := K) (V := V) Q hQ)

@[simp]
theorem prodNegCliffordModule_smul (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (a : CliffordAlgebra (Q.prod <| -Q)) (x : prodNegSpinorModule (K := K) (V := V)) :
    letI := prodNegCliffordModule (K := K) (V := V) Q hQ
    a • x = prodNegCliffordAction (K := K) (V := V) Q hQ a x := rfl

/-- The canonical chosen-model spin representation for `Q ⊕ (-Q)`. -/
noncomputable def prodNegSpinRepresentation (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    spinGroup (Q.prod <| -Q) →*
      Module.End K (prodNegSpinorModule (K := K) (V := V)) :=
  HyperbolicPresentation.spinRepresentation
    (K := K) (Q := ((Q.prod <| -Q) : QuadraticForm K (V × V)))
    (prodNegPresentation (K := K) (V := V) Q hQ)

/-- The canonical `spinGroup` action on the doubled chosen model. -/
noncomputable abbrev prodNegMulAction (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    MulAction (spinGroup (Q.prod <| -Q)) (prodNegSpinorModule (K := K) (V := V)) :=
  HyperbolicPresentation.spinMulAction
    (K := K) (Q := ((Q.prod <| -Q) : QuadraticForm K (V × V)))
    (prodNegPresentation (K := K) (V := V) Q hQ)

@[simp]
theorem prodNegMulAction_smul (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (g : spinGroup (Q.prod <| -Q)) (x : prodNegSpinorModule (K := K) (V := V)) :
    letI := prodNegMulAction (K := K) (V := V) Q hQ
    g • x = prodNegSpinRepresentation (K := K) (V := V) Q hQ g x := rfl

/-- The canonical chosen-model spin representation on the even half of `Q ⊕ (-Q)`. -/
noncomputable def evenProdNegSpinRepresentation (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    spinGroup (Q.prod <| -Q) →*
      Module.End K (evenProdNegSpinorModule (K := K) (V := V)) :=
  HyperbolicPresentation.evenSpinRepresentation
    (K := K) (Q := ((Q.prod <| -Q) : QuadraticForm K (V × V)))
    (prodNegPresentation (K := K) (V := V) Q hQ)

/-- The canonical chosen-model spin representation on the odd half of `Q ⊕ (-Q)`. -/
noncomputable def oddProdNegSpinRepresentation (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    spinGroup (Q.prod <| -Q) →*
      Module.End K (oddProdNegSpinorModule (K := K) (V := V)) :=
  HyperbolicPresentation.oddSpinRepresentation
    (K := K) (Q := ((Q.prod <| -Q) : QuadraticForm K (V × V)))
    (prodNegPresentation (K := K) (V := V) Q hQ)

/-- The doubled chosen spin representation preserves the even diagonal half-spin space. -/
theorem prodNegSpinRepresentation_mem_even (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {g : spinGroup (Q.prod <| -Q)} {x : prodNegSpinorModule (K := K) (V := V)}
    (hx : x ∈ evenProdNegSpinorModule (K := K) (V := V)) :
    prodNegSpinRepresentation (K := K) (V := V) Q hQ g x ∈
      evenProdNegSpinorModule (K := K) (V := V) := by
  exact HyperbolicPresentation.spinRepresentation_mem_even
    (K := K) (Q := ((Q.prod <| -Q) : QuadraticForm K (V × V)))
    (P := prodNegPresentation (K := K) (V := V) Q hQ) hx

/-- The doubled chosen spin representation preserves the odd diagonal half-spin space. -/
theorem prodNegSpinRepresentation_mem_odd (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {g : spinGroup (Q.prod <| -Q)} {x : prodNegSpinorModule (K := K) (V := V)}
    (hx : x ∈ oddProdNegSpinorModule (K := K) (V := V)) :
    prodNegSpinRepresentation (K := K) (V := V) Q hQ g x ∈
      oddProdNegSpinorModule (K := K) (V := V) := by
  exact HyperbolicPresentation.spinRepresentation_mem_odd
    (K := K) (Q := ((Q.prod <| -Q) : QuadraticForm K (V × V)))
    (P := prodNegPresentation (K := K) (V := V) Q hQ) hx

/-- The doubled form `Q ⊕ (-Q)` has Witt index `dim(V)`. -/
theorem wittIndex_prodNeg (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    QuadraticForm.wittIndex (((Q.prod <| -Q) : QuadraticForm K (V × V))) = Module.finrank K V := by
  rw [HyperbolicPresentation.wittIndex_eq_finrank
    (K := K) (Q := ((Q.prod <| -Q) : QuadraticForm K (V × V)))
    (P := prodNegPresentation (K := K) (V := V) Q hQ)]
  exact finrank_diagSubmodule (K := K) (V := V)

/-- The diagonal subspace is maximal totally isotropic for the doubled form `Q ⊕ (-Q)`. -/
theorem diagSubmodule_isMaximalTotallyIsotropic (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    QuadraticForm.IsMaximalTotallyIsotropic ((Q.prod <| -Q) : QuadraticForm K (V × V))
      (diagSubmodule (K := K) (V := V)) := by
  apply QuadraticForm.isMaximalTotallyIsotropic_of_finrank_eq_wittIndex
    (Q := ((Q.prod <| -Q) : QuadraticForm K (V × V)))
  · exact diagSubmodule_isTotallyIsotropic (K := K) (V := V) Q
  · rw [wittIndex_prodNeg (K := K) (V := V) Q hQ, finrank_diagSubmodule]

/-- The even diagonal half-spin space of `Q ⊕ (-Q)` has dimension `2^(dim(V) - 1)` in positive rank. -/
theorem finrank_evenProdNegSpinorModule (hV : 0 < Module.finrank K V) :
    Module.finrank K (evenProdNegSpinorModule (K := K) (V := V)) =
      2 ^ (Module.finrank K V - 1) := by
  have hdiag : 0 < Module.finrank K (diagSubmodule (K := K) (V := V)) := by
    simpa [finrank_diagSubmodule (K := K) (V := V)] using hV
  simpa [evenProdNegSpinorModule, finrank_diagSubmodule (K := K) (V := V)] using
    finrank_evenExterior (K := K) (diagSubmodule (K := K) (V := V)) hdiag

/-- The odd diagonal half-spin space of `Q ⊕ (-Q)` has dimension `2^(dim(V) - 1)` in positive rank. -/
theorem finrank_oddProdNegSpinorModule (hV : 0 < Module.finrank K V) :
    Module.finrank K (oddProdNegSpinorModule (K := K) (V := V)) =
      2 ^ (Module.finrank K V - 1) := by
  have hdiag : 0 < Module.finrank K (diagSubmodule (K := K) (V := V)) := by
    simpa [finrank_diagSubmodule (K := K) (V := V)] using hV
  simpa [oddProdNegSpinorModule, finrank_diagSubmodule (K := K) (V := V)] using
    finrank_oddExterior (K := K) (diagSubmodule (K := K) (V := V)) hdiag

end ProdNegTransport

end Spinor
