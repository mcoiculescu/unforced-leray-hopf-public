import UnforcedLeray.Lib.HeatR3.ConvOp
import UnforcedLeray.Lib.HeatR3.LpOp
import UnforcedLeray.Lib.HeatR3.Space
import UnforcedLeray.Lib.HeatR3.Bounded
import UnforcedLeray.Lib.HeatR3.Admissible
import UnforcedLeray.Lib.HeatR3.Smooth
import UnforcedLeray.Lib.HeatR3.Line
import UnforcedLeray.Lib.HeatR3.Continuity
import UnforcedLeray.Lib.HeatR3.Decay
import UnforcedLeray.Lib.HeatR3.HeatDecay
import UnforcedLeray.Lib.HeatR3.Similarity
import UnforcedLeray.Lib.HeatR3.Anisotropic
import UnforcedLeray.Lib.HeatR3.FTC
import UnforcedLeray.Lib.HeatR3.SubSelf
import UnforcedLeray.Lib.HeatR3.Joint
import UnforcedLeray.Lib.HeatR3.Smoothing
import UnforcedLeray.Lib.HeatR3.LineBridge
import UnforcedLeray.Lib.HeatR3.Comm
import UnforcedLeray.Lib.HeatR3.SimEquation
import UnforcedLeray.Lib.HeatR3.SimContinuity
import UnforcedLeray.Lib.HeatR3.SimSolenoidal
import UnforcedLeray.Lib.HeatR3.Generator
import UnforcedLeray.Lib.HeatR3.GroupDeriv
import UnforcedLeray.Lib.HeatR3.Duhamel
import UnforcedLeray.Lib.HeatR3.Transverse
import UnforcedLeray.Lib.HeatR3.Weighted
import UnforcedLeray.Lib.HeatR3.Mixed

/-!
# Heat semigroups on `ℝ^d`, on groups and on the line (Wave 2 block 2A HEAT-G, finished in Wave 3)

Main file of block 2A of the Lean build plan

`scoping/INF04-INF05-Heat.md` §5; decisions D1, D14, D17 of §3). Namespace
`UnforcedLeray.Heat` (the namespace of the compiled `lean/UnforcedLeray/Analysis/Heat`).
The single Gaussian module is `UnforcedLeray.Lib.Gaussian` (D14).

| Target | Module | Main declarations |
|---|---|---|
| T3 (BP1, BP2, D17) | `ConvOp`, `LpOp`, `Continuity`, `Comm` | `heatConv`, `heatAbs`, `eLpNorm_heatConv_le` (`1 ≤ p ≤ ∞`), `ae_integrable_heatIntegrand`, `heatConv_add_time`, `heatLp`, `heatLp_rep`, `norm_heatLp_le`, `heatLp_add`, `heatLp_continuousOn` (`p < ∞`), `heatLp_eq_integral`, `heatLp_comm` |
| T4 (`ℝ³` instance) | `Smoothing` | `fderiv_average_apply`, `eLpNorm_fderiv_average_apply_le` (`‖∂_w e^{θΔ}u‖_p ≤ cθ^{-1/2}|w|‖u‖_p`) |
| T4 (generic `G`, generator) | `Generator`, `GroupDeriv` | `gaussD1`, `hasDerivAt_heatConv_dir` (bounded data, every `x`), `gaussDt`, `hasDerivAt_gaussKernel_time`, `heatConvK`, `heatLpK`, `heatLp_eq_heatLpK`, `hasDerivAt_heatLp_time` (`p < ∞`) |
| T5 (BP2) | `Space` | `heatConv_space_eq_average`, `heatLp_space_two`, `average_isometry`, `average_dilate` |
| T7 | `Bounded`, `FTC` | `norm_average_le_of_bound`, `iteratedFDeriv_average`, `spaceDiv_average`, `hasDerivAt_average_time` (heat equation), `average_sub_eq_integral` (heat FTC) |
| T8 | `Admissible`, `Smooth`, `Joint` | `HeatAdmissible`, `.of_memLp`, `.of_inv_bound`, `integrable_heat`, `average_add'`, `average_add_time'`, `average_dilate'`, `contDiff_average`, `norm_iteratedFDeriv_average_le_kernel`, `continuousOn_average_joint` |
| T9 (BP3, BP4) | `Decay`, `HeatDecay`, `SubSelf` | `peetre`, `norm_average_le_weight`, `InvDistClass`, `.dilate`, `heat_vanishing_tail`, `InvDistClass.heat_decay`, `heat_sub_self_decay` (2.48) |
| T10 | `Similarity`, `SimEquation`, `SimContinuity`, `SimSolenoidal` | `simHeat`, `simHeat_eq`, `simHeat_periodic`, `simHeat_contDiff`, `simHeat_decay`, `InvDistClass.hasDerivAt_average_time`, `InvDistClass.hasStrictFDerivAt_average_joint`, `simHeat_equation`, `InvDistClass.dil_sub`, `InvDistClass.heat_decay_lin`, `simHeat_continuous_C0`, `simHeat_grad_continuous_L3`, `simHeat_hessian_continuous_L2`, `spaceDiv_average_eq_zero`, `simHeat_solenoidal` |
| T12 (+ T19 kernel bound) | `Anisotropic`, `Transverse`, `Mixed` | `kernel_factor`, `abs_pow_mul_iteratedDeriv_lineGauss_le`, `eLpNorm_pow_mul_iteratedDeriv_lineGauss_le`, `vsplit`, `measurePreserving_vsplit`, `mkPoint`, `norm_iteratedFDeriv_average_le_transverse`, `mixedNormHV`, `eLpNorm_average_mixed`, `eLpNorm_average_mixed_pow` |
| T18 (+ T2 in 1D, BP1, BP7) | `Line`, `LineBridge`, `Duhamel` | `lineGauss`, `eLpNorm_iteratedDeriv_lineGauss`, `lineHeat`, `eLpNorm_lineHeat_le`, `eLpNorm_lineHeat_of_L1`, `iteratedDeriv_lineHeat`, `eLpNorm_iteratedDeriv_lineHeat`, `lineHeat_eq_heatConv`, `lineHeat_add_time`, `hasDerivAt_lineHeat_data`, `lineDuhamel`, `hasDerivAt_lineDuhamel`, `deriv_lineDuhamel` |
| T19 (initial-data part) | `Weighted` | `pow_mul_iteratedDeriv_lineHeat`, `eLpNorm_pow_mul_iteratedDeriv_lineHeat_le`, `eLpNorm_lineGauss_eq`, `eLpNorm_pow_mul_iteratedDeriv_lineHeat_le_large` (`θ^{(m-b-1)/2+1/(2p)}`, B0181) |

Not built here: the `L^p` form of the directional derivative on a general group (the pointwise
heat integral at every `x` of `L^p` data needs `ι` to be measure-class surjective; the `ℝ³`
instance is `Smoothing`, the bounded-data form is `GroupDeriv`), the identification
`mean_stream_eq` of T18 (needs the averaged mild formulation
of the velocity), and the parts of T19 beyond the initial-data weighted bound: the Taylor
expansion with remainder of B0180 (`eq:st18-t00176`–`00178`), the Duhamel source term with
mixed moments, and the time derivatives `∂_s^ℓ`.

Conventions: heat time `θ` (the kernel of `e^{θΔ}` is `G_θ(x) = (4πθ)^{-d/2}e^{-|x|²/(4θ)}`,
risk R10 of the scoping note); every statement assumes `θ > 0`, and `heatLp` is the identity for
`θ ≤ 0`.
-/
