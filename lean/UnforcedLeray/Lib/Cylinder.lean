import UnforcedLeray.Lib.Cylinder.Basic
import UnforcedLeray.Lib.Cylinder.Weight
import UnforcedLeray.Lib.Cylinder.WeightDerivs
import UnforcedLeray.Lib.Cylinder.WeightCentred
import UnforcedLeray.Lib.Cylinder.Lebesgue
import UnforcedLeray.Lib.Cylinder.Modes
import UnforcedLeray.Lib.Cylinder.ModesWirtinger
import UnforcedLeray.Lib.Cylinder.CellModes
import UnforcedLeray.Lib.Cylinder.SupBound
import UnforcedLeray.Lib.Cylinder.Jq
import UnforcedLeray.Lib.Cylinder.IBP
import UnforcedLeray.Lib.Cylinder.Seam
import UnforcedLeray.Lib.Cylinder.SeamComplex
import UnforcedLeray.Lib.Cylinder.SmoothEnergy
import UnforcedLeray.Lib.Cylinder.Extension

/-!
# Periodic cylinder analysis, layer 0-1 (Wave 1, block 1E part 1: INF13 CY01-CY05, CY14)

Main file of the INF13 cylinder layer of the Lean build plan

`scoping/INF13-INF23-Cylinder.md` §5 Layers 0-1 and CY14).  Namespace `UnforcedLeray.Cyl`.

Carrier (decision D1): a cylinder field is a `c`-periodic function on `Plane = ℝ × ℝ`
(`IsPeriodic`), norms are integrals over the centred cell `cell c = [-c/2, c/2) × ℝ`, and
meridional vectors take values in `Vec2 = EuclideanSpace ℝ (Fin 2)`.  Weights (decision D12):
both the centred seam weight `ρc = 1 + q² + η²` and the smooth periodic weight
`ρw c = 1 + (c/π)² sin²(πq/c) + η²`, with the uniform equivalence `(4/π²) ρc ≤ ρw ≤ ρc` on the
cell.

| Target | Module | Main declarations |
|---|---|---|
| CY01 | `Basic` | `IsPeriodic`, `cell`, `cellμ`, `avgμ`, `partialQ`, `partialEta`, `curl`, `divergence`, `isAddFundamentalDomain_strip`, `lintegral_strip_eq_cell`, `integral_strip_eq_cell`, `lintegral_cell_comp_add`, `integral_cell_comp_add`, `integral_cell_eq_integral_integral`, `avgμ_univ_prod`, `integral_avgμ` |
| CY02 | `Weight`, `WeightDerivs`, `WeightCentred` | `ρw`, `ρc`, `contDiff_ρw`, `isPeriodic_ρw`, `ρw_le_ρc`, `ρw_comparable`, `rpow_ρw_comparable`, `rpow_neg_ρw_comparable`, `ρw_dilate`, `integrable_rpow_neg_ρc`, `setIntegral_rpow_neg_ρw_le`, `norm_iteratedFDeriv_rpow_ρw_le`; for `ρc`: `norm_iteratedFDeriv_ρc_le`, `norm_iteratedFDeriv_rpow_ρc_le`, `ρc_dilate`, `setIntegral_rpow_neg_ρc_le` (tex 4171-4184, 4569-4578; B0242, B0271) |
| CY03 | `Lebesgue` | `wμ`, `wμc`, `X`, `Xc`, `eLpNorm_wμ_le_wμc`, `eLpNorm_wμc_le_wμ`, `eLpNorm_one_cell_le`, `integral_norm_cell_le`, `circ`, `circCLM`, `norm_circCLM_le`, `X0`, `mem_X0`, `norm_pairing_le` (B0285, B0655) |
| CY04 | `Modes`, `ModesWirtinger`, `CellModes`, `SupBound`, `Jq` | `qAvg`, `qMode`, `qMode_zero`, `qMode_partialQ`, `hasSum_sq_qMode`, `norm_sq_qAvg_le`, `wirtinger_slice_variance`, `integral_norm_sub_qAvg_sq`, `wirtinger_slice` (slice forms); `hasSum_cell_parseval`, `enorm_qAvg_rpow_le`, `eLpNorm_qAvg_le`, `eLpNorm_qAvg_contract_weighted`, `eLpNorm_qAvg_cell_le`, `lintegral_cell_sub_qAvg_le`, `eLpNorm_sub_qAvg_le`, `eLpNorm_le_of_qAvg_eq_zero` (cell forms; B0158, B0172, B0176, B0566); `sq_norm_le_of_periodic`, `sq_norm_le_cyl`, `sq_sup_q_le` (B0183); `jqSymbol`, `Jq`, `fourierCoeff_Jq`, `fourierCoeff_Jq_mul`, `Jq_perLp_deriv`, `norm_Jq_le` (`c/(2π)`), `norm_Jq_le_div_pi` (`c/π`), `zeroMeanL2`, `JqZ`, `norm_JqZ_le` (tex 9077-9085, 12246-12260; B0566, B0828) |
| CY05 | `IBP`, `Seam`, `SeamComplex`, `SmoothEnergy` | `integral_cell_deriv_q`, `integral_cell_deriv_eta`, `integral_cell_partialQ_mul`, `integral_cell_partialEta_mul`, `integral_cell_curl_eq_zero`, `integral_cell_divergence_eq_zero` (B0285, B0144); `weighted_laplacian_identity`, `weighted_laplacian_le_seam_core`, `weighted_laplacian_le_seam`, `re_weighted_laplacian_le_seam`, `laplacian_rpow_ρc`, `laplacian_rpow_ρc_le`, `weighted_laplacian_le_seam_const`, `weighted_laplacian_smooth`, `weighted_laplacian_le_smooth`, `transport_antisymm`, `re_transport_antisymm` (tex 4171-4184, 6494-6518; B0242, B0343) |
| CY14 | `Extension` | `hμ`, `Hm`, `Ic`, `norm_Ic`, `Rc`, `Rc_comp_Ic`, `coeFn_Rc`, `PiC` (`Π_c`), `PiC_idem`, `isSelfAdjoint_PiC` (tex 6166-6188; B0319, B0342) |

Deviations from the scoping signatures, each recorded in its module:
* the seam inequality, its smooth-weight analogue and transport antisymmetry are proved for
  `C²` (resp. `C¹`) periodic fields with compact support in `η`; the general weighted-`H²`
  case is the density step of CY06, not built here (the exact identity
  `weighted_laplacian_identity` is stated under bare integrability hypotheses);
* `Ic` is defined on the centred space `Xc c m`, not on `X c m`, since only then is it an
  isometry and `Rc ∘ Ic = id`;
* `Πc` is spelled `PiC` (`Π` is reserved);
* `Jq` acts on `L²(ℝ/cℤ)` with normalised Haar measure (D2); its operator norm does not depend
  on the normalisation;
* CY04 cell forms (`CellModes`): the inequalities are stated in `ℝ≥0∞` (`eLpNorm`,
  `lintegral`), so no Bochner junk value enters; `eLpNorm_qAvg_le` is proved for every
  `1 ≤ p < ∞` with the constant `c^{-1/p}`; `qAvg_contract_weighted` is
  `eLpNorm_qAvg_contract_weighted`, for a measurable real weight `w(η)` and every
  `1 ≤ p < ∞`; `norm_sub_qAvg_le` is `eLpNorm_sub_qAvg_le` (and its zero-mean case
  `eLpNorm_le_of_qAvg_eq_zero`) for `C¹` periodic fields, the classical form of the weak
  statement, as for `qMode_partialQ`;
* CY04 `sq_sup_q_le` (`SupBound`) is proved for `C¹` periodic fields (classical form of
  `H¹(ℝ/cℤ) ⊂ L^∞`, B0183), together with the pointwise form `sq_norm_le_cyl`;
* CY02 for `ρc` (`WeightCentred`): the derivative bound has a constant independent of `z`
  (`ρc` does not depend on the period); `setIntegral_rpow_neg_ρc_le` holds for every period.
-/
