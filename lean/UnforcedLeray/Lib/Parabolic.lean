import UnforcedLeray.Lib.Parabolic.Kernel
import UnforcedLeray.Lib.Parabolic.Hormander
import UnforcedLeray.Lib.Parabolic.Tests
import UnforcedLeray.Lib.Parabolic.Fourier
import UnforcedLeray.Lib.Parabolic.Duhamel
import UnforcedLeray.Lib.Parabolic.TimeYoung
import UnforcedLeray.Lib.Parabolic.L2Bound
import UnforcedLeray.Lib.Parabolic.L2Op
import UnforcedLeray.Lib.Parabolic.Adjoint
import UnforcedLeray.Lib.Parabolic.OffSupport
import UnforcedLeray.Lib.Parabolic.LqBound
import UnforcedLeray.Lib.Parabolic.Fundamental
import UnforcedLeray.Lib.Parabolic.QTwo

/-!
# Parabolic maximal regularity for the causal heat kernel (Wave 2, block 2C PARAB: INF02)

Main file of block 2C of the Lean build plan

`q = 2` case of T8, T10 and T7 of the scoping note `scoping/INF02-FabesRiviere.md` §5, built
under decision D4 (the parabolic instance, weights `(2,1,…,1)`, of the anisotropic
Calderón–Zygmund core `Lib/CZCore`; no maximal function) and D14 (Gaussian facts from
`Lib/Gaussian`). Namespace `UnforcedLeray.Parabolic`.

Manuscript: the lemma eq:free-stress-11 (`paper/main.tex` lines 7447–7477, blueprint unit
B0423): for `1 < q < ∞`, `ν > 0`, `‖ν D_x² u‖_q + ‖∂_θ u‖_q ≤ C_{d,q} ‖F‖_q` when
`(∂_θ - νΔ_x) u = F`. The manuscript cites Fabes–Rivière for the singular-integral bound of
the causal kernel `1_{θ>0}∂_{ij}H_θ` (line 7466); here that bound is proved from the CZ core.
Nothing here proves Theorem A or `UnforcedLeray.MainClaim`.

| Target | Module | Main declarations |
|---|---|---|
| T5 (pointwise) | `Kernel` | `PS`, `hessG`, `causalKernel`, `hessG_eq_scale`, `abs_hessG_le` (size), `abs_hessG_le_mul`, `exists_hasDerivAt_hessG`, `abs_hessG_sub_le`, `abs_causalKernel_time_sub_le`, `abs_causalKernel_sub_le` (pointwise Hörmander), `causalKernel_neg_space`, `measurable_causalKernel` |
| T5 (integral) | `Hormander` | `parWeights`, `homDim_parWeights`, `psEquiv`, `measurePreserving_psEquiv`, `causalKernelCoord`, `abs_causalKernelCoord_le` (size in the CZ gauge), `hormander_causalKernelCoord` (Hörmander), `hormander_comp_neg` (reflected kernel) |
| T6 (tests) | `Tests`, `Duhamel` | `IsSTTest`, `dirD`, `sD`, `tD`, `sD2`, `sLap`, `causalHeat`, `locallyIntegrable_causalHeat`, `duhamel`, `contDiff_duhamel`, `dirD_duhamel`, `secondDerivTest`, `sD2_duhamel` |
| T6 (BP-A) | `Fourier`, `TimeYoung`, `L2Bound` | `gaussKernel_eq_fourier`, `pairing_heat_eq`, `fourier_dirDeriv`, `lintegral_enorm_fourier_sq`, `lintegral_time_conv_le`, `enorm_pairing_secondDerivTest_le` |
| T6 (`L²` operator) | `L2Op` | `eLpNorm_secondDerivTest_le`, `testSpace`, `toL2`, `denseRange_toL2`, `secondDerivOp`, `secondDerivOp_toLp`, `norm_secondDerivOp_le` |
| T6 (transpose) | `Adjoint` | `trev`, `sD2_comm`, `integral_mul_sD2`, `backTest`, `integral_mul_secondDerivTest_eq`, `backOp`, `backOp_toLp`, `integral_secondDerivOp_mul` |
| T6 (off support) | `OffSupport` | `causalKernelNu`, `backTest_offSupport`, `secondDerivOp_offSupport` |
| T7 | `LqBound` | `backOp_offSupport`, `pullL2`, `pushL2`, `isCZConvolution_coord`, `secondDerivOp_eLpNorm_le`, `timeDerivOp`, `timeDerivOp_eLpNorm_le` |
| T8 (`q = 2`, first step) | `Fundamental` | `fderiv_gaussKernel_one_apply`, `integral_gaussKernel_scale`, `integral_gauss_mul_inner` (Gaussian integration by parts), `heatAvg`, `hasDerivAt_heatAvg`, `duhamel_heatOp` (`H_ν ⋆ (∂_t - νΔ)g = g` on tests) |
| T8 (`q = 2`), T10 | `QTwo` | `backTest_heatAdj` (`-∂_tΨ - νΔΨ = ∂_i∂_jφ`), `sD_backTest`, `heatAdj_mul`, `integral_mul_sD2_eq` (identification), `eLpNorm_smul_secondDerivOp_le`, `heat_maximal_regularity_two` |
| T10 (operator form) | `L2Op`, `LqBound` | `norm_smul_secondDerivOp_le` (`‖ν ∂_i∂_j (∂_t - νΔ)^{-1}‖_{L²→L²} ≤ 1`), `norm_timeDerivOp_le` (`≤ 1 + d`) |

Deviations from the indicative signatures of `INF02-FabesRiviere.md` §5:

* `secondDerivOp` carries the viscosity: `secondDerivOp hν i j` is `∂_i∂_j (∂_t - νΔ)^{-1}`, and
  `norm_secondDerivOp_le` reads `‖secondDerivOp hν i j‖ ≤ ν⁻¹` (the note's `≤ 1` is `ν = 1`).
* The Hörmander condition is stated, as the CZ core consumes it, for the transported kernel
  `causalKernelCoord = causalKernel ∘ psEquiv` on `ℝ^{1+d}` with the core's gauge
  `max(|t|^{1/2}, |x_1|, …, |x_d|)` and as a lower integral (`∫⁻`), not with the note's gauge
  `max(√|t|, |x|)` and a Bochner integral.
* `secondDerivOp_eLpNorm_le` is proved at `ν = 1`; the `ν`-scaling belongs to INF02 T8.
* `heat_maximal_regularity_two` (T8 at `q = 2`, T10) does not assume that `u` is compactly
  supported in time (the manuscript's hypothesis): at `q = 2` the identification needs only
  `u, F ∈ L²`. Weak derivatives are stated as integral identities against `IsSTTest` tests.

Not built here: INF02 T8 for `q ≠ 2` (identification of the `L^q` extension with the weak
derivatives, mollification, `ν`-scaling of the `L^q` constant), which is Wave 3 block 3D PARAB2,
and INF02 T9 (cylinder).
-/
