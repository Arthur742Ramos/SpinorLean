# SpinorLean theorem index

This index maps the paper's theorem-facing statements to the Lean declarations that support them.
It is intentionally reader-facing: the declarations below are the stable entry points to inspect
when checking that the artifact matches the paper.

## Paper results and Lean declarations

| Paper statement | Main Lean declarations |
| --- | --- |
| Chosen exterior spinor package (`thm:chosen-spinor-package`) | `Spinor.HyperbolicPresentation`; `HyperbolicPresentation.spinorModule`; `HyperbolicPresentation.cliffordAction`; `HyperbolicPresentation.spinRepresentation`; `HyperbolicPresentation.cliffordEquivEnd`; `HyperbolicPresentation.cliffordEquivMatrix`; `splitSpinorModule`; `positiveHalfSpinorModule`; `negativeHalfSpinorModule` |
| Split Clifford matrix-unit / full matrix model (`thm:matrix-units-split`) | `splitCliffordAction_surjective`; `splitCliffordAction_injective`; `HyperbolicPresentation.cliffordEquivEnd`; `splitWittCliffordEquivMatrix` |
| Even Clifford product and half-spin package (`cor:even-half-spin`) | `evenSplitCliffordEquivProdEnd`; `evenSplitCliffordAction_isSimpleModule`; `oddSplitCliffordAction_isSimpleModule`; `not_nonempty_evenOddSplitCliffordLinearEquiv`; `positiveHalfSpinorModule_eq_evenWittExterior`; `negativeHalfSpinorModule_eq_oddWittExterior`; `splitSpinor_chiral_correspondence` |
| Transport from split/Witt presentations (`prop:transport-split`) | `HyperbolicPresentation.ofIsCompl`; `wittPresentation`; `splitWittPresentation`; `splitSpinorCliffordAction_sq_apply`; `splitSpinorCliffordAction_injective`; `splitSpinorModule_finrank`; `positiveHalfSpinorModule_finrank`; `negativeHalfSpinorModule_finrank` |
| Spin-to-isometry map and special orthogonal target | `spinIsometryRepresentation`; `spinSpecialOrthogonalRepresentationFiniteDimensional`; `spinLinearRepresentation_det_eq_one` |
| Positive split-rank kernel and non-factorization (`thm:kernel-nonfactor-split-line`) | `HyperbolicPresentation.spinRepresentation_not_factor_through_isometry_of_pos_finrank`; `splitSpinRepresentation_not_factor_through_isometry`; `positiveHalfSpinRepresentation_not_factor_through_isometry`; `negativeHalfSpinRepresentation_not_factor_through_isometry`; `spinSpecialOrthogonalRepresentationFiniteDimensional_range_dualProdLine_eq_squareScalingSubgroup` |
| Projective descent (`prop:projective-descent`) | `HyperbolicPresentation.submodule_map_spinRepresentation_eq_of_spinIsometryRepresentation_eq`; `splitSpinorSubmodule_map_spinRepresentation_eq_of_spinIsometryRepresentation_eq`; `positiveHalfSpinorSubmodule_map_spinRepresentation_eq_of_spinIsometryRepresentation_eq`; `negativeHalfSpinorSubmodule_map_spinRepresentation_eq_of_spinIsometryRepresentation_eq`; `splitSpinorSubmoduleImageAction`; `positiveHalfSpinorSubmoduleImageAction`; `negativeHalfSpinorSubmoduleImageAction` |
| Levi lifts act projectively as exterior action (`thm:levi-projective-exterior`) | `eq_algebraMap_of_forall_contractionAction_eq_zero`; `splitCliffordAction_eq_smul_exteriorMap_of_spinSpecialOrthogonalRepresentation_eq`; `splitCliffordAction_eq_units_smul_exteriorMap_of_spinSpecialOrthogonalRepresentation_eq`; `splitCliffordAction_apply_one_and_topExteriorGenerator_of` |
| Hyperbolic transvection Clifford unit (`prop:transvection-unit`) | `dualProdTransvectionCliffordUnit`; `coe_dualProdTransvectionCliffordUnit`; `dualProdTransvectionCliffordUnit_inv_eq`; `dualProdTransvectionCliffordUnit_mem_unitary`; `dualProdTransvectionCliffordUnit_mem_even`; `dualProdTransvectionCliffordUnit_conjAct_eq_transvection`; `splitCliffordAction_dualProdTransvectionCliffordUnit_eq_exteriorMap_transvection` |
| Chosen-line square scaling and torus action (`prop:chosen-line-square`, `cor:torus-transvection`, `cor:internal-clifford-torus`, `cor:one-line-semidirect`) | `spinSpecialOrthogonalPairGenerator`; `lineScalingLinearEquiv`; `spinSpecialOrthogonalPairGenerator_eq_lineScalingLinearEquiv`; `lineScalingLinearEquiv_mul_transvection_mul_symm_eq`; `splitCliffordAction_spinIotaPairOfQuadraticEqNegOne_eq_smul_exteriorMap_lineScaling` |
| Square-determinant Levi factorization and explicit chosen-model lift (`thm:square-det-levi`) | `splitCliffordAction_list_prod_basisTransvectionCliffordUnit_eq_exteriorMap_prod`; `exists_basisScalingLinearEquivCliffordUnit_eq_smul_exteriorMap_of_prod_eq_sq`; `exists_linearEquivCliffordUnit_eq_smul_exteriorMap_of_det_eq_sq` |
| Exact split-line image and double-cover criterion (`prop:split-line-square`) | `spinSpecialOrthogonalPairGeneratorSet_dualProdLine_closure_eq_squareScalingSubgroup`; `spinSpecialOrthogonalRepresentationFiniteDimensional_range_dualProdLine_eq_squareScalingSubgroup`; `spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_dualProdLine_iff_square_surjective`; `spinSpecialOrthogonalRepresentationFiniteDimensional_not_surjective_dualProdLine_of_exists_nonsquare_unit`; `spinSpecialOrthogonalRepresentationFiniteDimensional_covering_dualProdLine_iff_square_surjective` |

## Verification surface

The companion artifact is checked by:

```bash
bash scripts/verify.sh
```

On Windows PowerShell, use `.\scripts\verify.ps1`. The proof-hole check is expected to return no
matches. GitHub Actions runs the same build and no-hole checks on pushes and pull requests.
`Spinor.TheoremIndex` is imported by `Spinor.lean`, so the normal build also checks that the
paper-facing declaration names in this index still resolve.
