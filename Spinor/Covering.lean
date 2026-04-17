import Spinor.ProdNeg
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod

/-!
  Finite-dimensional kernel packaging for the ambient spin covering map.

  The remaining obstruction in `Spinor.OrthogonalAction` is the step from
  "kernel elements commute with everything" to "kernel elements are scalar".
  This file resolves that step in finite-dimensional nondegenerate rank by
  passing to the canonical doubled hyperbolic presentation `Q ⊕ (-Q)`,
  where the chosen-model Clifford action is an endomorphism algebra.
-/

namespace Spinor

universe uK uV

open scoped TensorProduct

variable {K : Type uK} [Field K] [Invertible (2 : K)]
variable {V : Type uV} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

omit [Invertible (2 : K)] in
private theorem prodEquiv_comp_map_inl :
    (CliffordAlgebra.prodEquiv Q (-Q)).toAlgHom.comp
        (CliffordAlgebra.map (QuadraticMap.Isometry.inl Q (-Q))) =
      GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd Q)
        (CliffordAlgebra.evenOdd (-Q)) := by
  apply CliffordAlgebra.hom_ext
  ext v
  simp [CliffordAlgebra.ofProd_ι_mk]

/-- In finite-dimensional nondegenerate rank, an even Clifford element commuting with every
Clifford element is scalar. -/
theorem even_eq_algebraMap_of_commute [FiniteDimensional K V] (hQ : Q.Nondegenerate)
    {a : CliffordAlgebra Q} (ha : a ∈ CliffordAlgebra.even Q)
    (hcomm : ∀ b : CliffordAlgebra Q, Commute a b) :
    ∃ r : K, a = algebraMap K (CliffordAlgebra Q) r := by
  let inlQ : Q →qᵢ (Q.prod <| -Q) := QuadraticMap.Isometry.inl Q (-Q)
  let inrQ : (-Q) →qᵢ (Q.prod <| -Q) := QuadraticMap.Isometry.inr Q (-Q)
  let aLift : CliffordAlgebra (Q.prod <| -Q) := CliffordAlgebra.map inlQ a
  have hcommLift : ∀ b : CliffordAlgebra (Q.prod <| -Q), Commute aLift b := by
    intro b
    refine CliffordAlgebra.induction ?_ ?_ ?_ ?_ b
    · intro r
      change Commute aLift (algebraMap K (CliffordAlgebra (Q.prod <| -Q)) r)
      simpa [aLift] using
        (Algebra.commutes (A := CliffordAlgebra (Q.prod <| -Q)) r (CliffordAlgebra.map inlQ a)).symm
    · rintro ⟨v, w⟩
      have hleft :
          Commute aLift (CliffordAlgebra.map inlQ (CliffordAlgebra.ι Q v)) := by
        change Commute (CliffordAlgebra.map inlQ a)
          (CliffordAlgebra.map inlQ (CliffordAlgebra.ι Q v))
        simpa [Commute, map_mul] using
          congrArg (CliffordAlgebra.map inlQ) (hcomm (CliffordAlgebra.ι Q v)).eq
      have hright :
          Commute aLift (CliffordAlgebra.map inrQ (CliffordAlgebra.ι (-Q) w)) := by
        simpa [aLift, inlQ, inrQ] using
          (CliffordAlgebra.commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_left
            (f₁ := inlQ) (f₂ := inrQ) (hf := QuadraticMap.IsOrtho.inl_inr)
            (m₁ := a) (m₂ := CliffordAlgebra.ι (-Q) w) ha
            (CliffordAlgebra.ι_mem_evenOdd_one (Q := -Q) w))
      have hsplit :
          CliffordAlgebra.ι (Q.prod <| -Q) (v, w) =
            CliffordAlgebra.map inlQ (CliffordAlgebra.ι Q v) +
              CliffordAlgebra.map inrQ (CliffordAlgebra.ι (-Q) w) := by
        rw [show (v, w) = (v, 0) + (0, w) by simp]
        rw [map_add, CliffordAlgebra.map_apply_ι, CliffordAlgebra.map_apply_ι]
        rfl
      rw [hsplit]
      exact hleft.add_right hright
    · intro x y hx hy
      exact hx.mul_right hy
    · intro x y hx hy
      exact hx.add_right hy
  let P := prodNegPresentation (K := K) (V := V) Q hQ
  rcases hyperbolicClifford_eq_algebraMap_of_commute
      (K := K) (Q := ((Q.prod <| -Q) : QuadraticForm K (V × V))) (W := P.W) P.iso
      (a := aLift) hcommLift with ⟨r, hr⟩
  let scalarRight :
      CliffordAlgebra (-Q) →ₗ[K] K :=
    ((Algebra.linearMap K (CliffordAlgebra (-Q))).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (cliffordAlgebraMap_injective (Q := -Q)))).choose
  have hscalarRight :
      scalarRight.comp (Algebra.linearMap K (CliffordAlgebra (-Q))) = LinearMap.id :=
    ((Algebra.linearMap K (CliffordAlgebra (-Q))).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (cliffordAlgebraMap_injective (Q := -Q)))).choose_spec
  have hscalarRight_apply (r : K) :
      scalarRight (algebraMap K (CliffordAlgebra (-Q)) r) = r := by
    simpa using congrArg (fun f : K →ₗ[K] K => f r) hscalarRight
  have htensor :
      GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd Q)
          (CliffordAlgebra.evenOdd (-Q)) a =
        algebraMap K
          (CliffordAlgebra.evenOdd Q ᵍ⊗[K] CliffordAlgebra.evenOdd (-Q)) r := by
    calc
      GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd Q)
            (CliffordAlgebra.evenOdd (-Q)) a =
          CliffordAlgebra.prodEquiv Q (-Q) (CliffordAlgebra.map inlQ a) := by
            symm
            simpa [AlgHom.comp_apply] using
              congrArg
                (fun f :
                  CliffordAlgebra Q →ₐ[K]
                    CliffordAlgebra.evenOdd Q ᵍ⊗[K] CliffordAlgebra.evenOdd (-Q) => f a)
                (prodEquiv_comp_map_inl (Q := Q))
      _ = CliffordAlgebra.prodEquiv Q (-Q)
            (algebraMap K (CliffordAlgebra (Q.prod <| -Q)) r) := by
            simpa [aLift] using congrArg (CliffordAlgebra.prodEquiv Q (-Q)) hr
      _ = algebraMap K
            (CliffordAlgebra.evenOdd Q ᵍ⊗[K] CliffordAlgebra.evenOdd (-Q)) r := by
            simp
  refine ⟨r, ?_⟩
  have hmap :
      (TensorProduct.map LinearMap.id scalarRight)
          (GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd Q)
            (CliffordAlgebra.evenOdd (-Q)) a) =
        (TensorProduct.map LinearMap.id scalarRight)
          (algebraMap K
            (CliffordAlgebra.evenOdd Q ᵍ⊗[K] CliffordAlgebra.evenOdd (-Q)) r) := by
    simpa [GradedTensorProduct.algebraMap_def] using
      congrArg (TensorProduct.map LinearMap.id scalarRight) htensor
  have hmap' :
      a ⊗ₜ[K] scalarRight (1 : CliffordAlgebra (-Q)) =
        algebraMap K (CliffordAlgebra Q) r ⊗ₜ[K] scalarRight (1 : CliffordAlgebra (-Q)) := by
    simpa [TensorProduct.map_tmul] using hmap
  have hsmul :
      scalarRight (1 : CliffordAlgebra (-Q)) • a =
        scalarRight (1 : CliffordAlgebra (-Q)) • algebraMap K (CliffordAlgebra Q) r := by
    simpa [GradedTensorProduct.algebraMap_def, TensorProduct.map_tmul, TensorProduct.rid_tmul] using
      congrArg (TensorProduct.rid K (CliffordAlgebra Q)) hmap'
  have hscalarOne : scalarRight (1 : CliffordAlgebra (-Q)) = 1 := by
    simpa using hscalarRight_apply (r := 1)
  simpa [hscalarOne] using hsmul

/-- In finite-dimensional nondegenerate rank, the ambient spin-to-isometry kernel is exactly the
scalar elements `±1`. -/
theorem spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one [FiniteDimensional K V]
    (hQ : Q.Nondegenerate) (x : spinGroup Q) :
    spinIsometryRepresentation (Q := Q) x = 1 ↔
      (x : CliffordAlgebra Q) = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  refine spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one_of_kernel_scalars
    (Q := Q) ?_ x
  intro y hy
  exact even_eq_algebraMap_of_commute (Q := Q) hQ
    (ha := spinGroup.mem_even y.property)
    (hcomm := commute_of_spinIsometryRepresentation_eq_one (Q := Q) y hy)

end Spinor
