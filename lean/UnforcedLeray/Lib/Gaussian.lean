import UnforcedLeray.Lib.Gaussian.Kernel
import UnforcedLeray.Lib.Gaussian.Absorb
import UnforcedLeray.Lib.Gaussian.IteratedDeriv
import UnforcedLeray.Lib.Gaussian.LpNorm
import UnforcedLeray.Lib.Gaussian.SpaceTime
import UnforcedLeray.Lib.Gaussian.GammaToolkit
import UnforcedLeray.Lib.Gaussian.RadialMoments
import UnforcedLeray.Lib.Gaussian.LatticeSum
import UnforcedLeray.Lib.Gaussian.Tilt
import UnforcedLeray.Lib.Gaussian.Periodization
import UnforcedLeray.Lib.Gaussian.PeriodizationCell
import UnforcedLeray.Lib.Gaussian.HeatDilation
import UnforcedLeray.Lib.Gaussian.DistinctCenter
import UnforcedLeray.Lib.Gaussian.CscSquared
import UnforcedLeray.Lib.Gaussian.HeatDilationFlow
import UnforcedLeray.Lib.Gaussian.MovingCell
import UnforcedLeray.Lib.Gaussian.WeightedCell

/-!
# Gaussian integrals, lattice sums and periodization (Wave 1, block 1B part 2: INF22 G1–G10)

Main file of the Gaussian layer of the Lean build plan

`scoping/INF22-INF27-Kernels.md` §5 Layer G, bypasses BP9–BP11). Namespace
`UnforcedLeray.Gaussian`. Decision D14: this is the single generic-dimension Gaussian module
(INF22 G1 = INF04 T1–T2 = the Gaussian part of INF02 T5) and the single csc² lattice sum (G10,
through Mathlib `Cotangent.lean`; INF20 T20.5 is not built).

| Target | Module | Main declarations |
|---|---|---|
| G1 (BP3; INF04 T1–T2, INF02 T5) | `Kernel`, `IteratedDeriv` | `gaussKernel`, `integral_gaussKernel`, `memLp_gaussKernel`, `eLpNorm_gaussKernel`, `integral_gaussKernel_mul_gaussKernel` (semigroup), `gaussKernel_three_eq` (bridge to the compiled `Heat.kernel`), `norm_iteratedFDeriv_gaussKernel_le`, `norm_iteratedFDeriv_gaussKernel_le_parabolic` |
| G2 | `Absorb` | `rpow_mul_exp_le`, `sup_time_le` |
| G3 | `LpNorm`, `SpaceTime` | `eLpNorm_iteratedFDeriv_gaussKernel` (exact scaling), `eLpNorm_iteratedFDeriv_gaussKernel_le`, `causalKernel`, `memLp_causalKernel_iff`, `memLp_causalKernel_three_iff` (B0448–B0450) |
| G4 | `GammaToolkit` | `integral_rpow_mul_exp_neg_mul`, `integral_inverseTime_window_le`, `integral_one_add_rpow_mul_exp_le` |
| G5 | `RadialMoments` | `integral_pow_odd_gauss`, `quadrupole_64` (B0850), `integral_sin_sq_mul_exp_two` (B0364, B0850) |
| G6 (BP9) | `LatticeSum` | `tsum_gauss_shift_le` (≤ 10), `summable_gauss_shift`, `tsum_gauss_ne_zero_le` (≤ 18 e^{-c²/(8a)}), `tsum_mode_tail_le`, `tsum_pow_mul_gauss_ne_zero_le` |
| G7 | `Periodization`, `PeriodizationCell`, `HeatDilation`, `HeatDilationFlow`, `MovingCell`, `WeightedCell` | `periodize`, `summable_periodize`, `periodize_add_period`, `iteratedFDeriv_periodize`, `contDiff_periodize`, `norm_periodize_le_of_gauss`, `integral_cell_periodize`, `integral_cell_weight_periodize`, `lintegral_cell_sq_norm_periodize_le_of_gauss`, `heatDilation`, `integral_sq_snd_heatDilation`, `integral_cell_sq_periodize_heatDilation`; item 5 second half (B0317, B0333): `laplacian_periodize`, `hasDerivAt_periodize_heatDilation`, `laplacian_sub_deriv_heatDilation`, `laplacian_sub_deriv_periodize_heatDilation`, `hasDerivAt_periodize_period`, `fderiv_periodize_apply_self`, `movingCell_identity`, `movingCell_identity_dual`; lemma 6 weighted part (B0147, B0894): `weight_mul_norm_periodize_le_of_gauss`, `jbracket_mul_norm_periodize_le_of_gauss`, `lintegral_cell_weight_sq_norm_periodize_le`, `lintegral_cell_weight_sq_norm_periodize_le_of_gauss`, `lintegral_cell_jbracket_sq_norm_periodize_le_of_gauss` |
| G8 (BP11) | `DistinctCenter` | `gauss_mul_gauss`, `lattice_gauss_mul_gauss`, `distinctPairsEquiv`, `tsum_distinct_center_le`, `tsum_norm_mul_norm_distinct_le`, `lintegral_cell_sq_distinct_le`, `mul_exp_neg_sq_div_le` |
| G9 | `Tilt` | `exp_neg_sq_div_four_le_tilt`, `tsum_periodized_gauss_tilt_le`, `tsum_poly_periodized_gauss_tilt_le` (B0169) |
| G10 (BP10) | `CscSquared` | `tsum_inv_sq_eq_csc_sq`, `latticeInvSq_eq`, `norm_iteratedDeriv_latticeInvSq_le` (B0233, B0297) |

G7 item 5, second half (`HeatDilationFlow`, `MovingCell`): `(Δ - ∂_a)P_c[a^{-2}q(·/√a)] =
a^{-1}P_c[a^{-2}(Dq)(·/√a)]` with `D = Δ + ½y·∇ + 2` (B0317, tex 6138–6147), and the moving-cell
identities `ϑD(P_dq) - ∂_z(P_dq) = ϑP_dDq`, `ϑD^#(P_dg) + ∂_z(P_dg) = ϑP_dD^#g` (B0333, tex
6319–6329), for `C²` `q` with translate bounds `C(1+|q|)^{-s}`, `s > 1`, on `q`, `(1+‖y‖)‖Dq‖`
and `‖D²q‖` (the Laplacian is `Cyl.laplacian` of `Lib/Cylinder/IBP.lean`). G7 lemma 6, weighted
part (`WeightedCell`): for each `m ≥ 0`, `(1+η²/a)^m‖P_cf‖ ≤ K_mA` and
`∫_cell (1+η²/a)^m‖P_cf‖² ≤ K_mA²a` under `‖f‖ ≤ Ae^{-|z|²/(4a)}`, `0 < a ≤ c²`, and the fixed
weight `⟨η⟩^{2m}` versions for `1 ≤ a ≤ c²` (factor `a^m`).

Not built here: a termwise formula for the derivatives of the csc² series (its identity and
derivative bounds are proved).
-/
