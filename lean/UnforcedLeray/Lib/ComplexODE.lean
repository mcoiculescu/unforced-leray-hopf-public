import UnforcedLeray.Lib.ComplexODE.NeutralSolution
import UnforcedLeray.Lib.ComplexODE.L1Dependence
import UnforcedLeray.Lib.ComplexODE.Sturm
import UnforcedLeray.Lib.ComplexODE.NeutralReal
import UnforcedLeray.Lib.ComplexODE.NeutralGroundState
import UnforcedLeray.Lib.ComplexODE.CauchyLimit
import UnforcedLeray.Lib.ComplexODE.CriticalCauchy
import UnforcedLeray.Lib.ComplexODE.QuantitativeL1
import UnforcedLeray.Lib.ComplexODE.CauchyKernelLog
import UnforcedLeray.Lib.ComplexODE.QuantitativeLog
import UnforcedLeray.Lib.ComplexODE.PrincipalValue
import UnforcedLeray.Lib.ComplexODE.CriticalPerturbation
import UnforcedLeray.Lib.ComplexODE.ZeroExistence

/-!
# Linear ODE with complex parameters: the annular Rayleigh layer (Wave 1, block 1H part 3: INF18 O1–O3)

Main file of the INF18 layer of the Lean build plan

`scoping/INF10-INF12-INF18-Planar.md` §5 Level O, bypass B8 route A). The results are about
the Gaussian Rayleigh equation in logarithmic radius on a finite log-annulus, in the compiled
Evans framework (`lean/UnforcedLeray/Analysis/Rayleigh/Evans/*`). Blueprint unit B0034
(`paper/main.tex` lines 1001--1021, eqs. st18-t00032--t00033); the ODE replacements of the
neutral counting B0028--B0029 (lines 941--948).

Namespaces: `UnforcedLeray.Rayleigh.Evans` (Gaussian statements, as in the compiled Evans
layer) and `UnforcedLeray.ComplexODE` (generic real and complex analysis).

| Target | Module | Main declarations |
|---|---|---|
| inputs (copied drafts) | `NeutralSolution`, `L1Dependence` | `neutralNormalizedF`, `neutralEvansFunction`, `neutralNormalized_conj`, `norm_sub_le_integral_of_isSolOn`, `sol_tendstoUniformlyOn_of_integral_coefficients` |
| O1 annular neutral ground state | `Sturm`, `NeutralReal`, `NeutralGroundState` | `sturm_comparison_false`, `exists_first_zero`, `neutralU_pos_of_dirichlet`, `neutral_dirichlet_unique`, `exists_neutral_dirichlet_of_not_pos`, `exists_trial_wavenumber`, **`exists_dirichlet_neutral`** |
| O2 nontangential critical-layer limit | `CauchyLimit`, `CriticalCauchy`, `PrincipalValue` | `tendsto_integral_inv_linear`, `tendsto_integral_cauchy_remainder`, `tendsto_integral_cauchy_cone`, `Iplus`, `Iplus_im`, **`tendsto_critical_cauchy`**, `intervalIntegrable_Iplus_integrand` |
| O3 quantitative L¹ dependence | `QuantitativeL1`, `CauchyKernelLog`, `QuantitativeLog` | `rayleighPotential_sub_neutral`, `neutralPerturbationSize`, **`norm_normalizedPair_sub_neutral_le`**, **`norm_normalizedF_sub_neutral_le`**, `exists_integral_Wlog_div_norm_le_log`, **`norm_normalizedPair_sub_neutral_le_log`** |
| O4/O5 inputs (copied drafts) | `CriticalPerturbation`, `ZeroExistence` | `evansFunction_critical_perturbation`, `exists_zero_of_center_norm_lt_sphere`, `exists_zero_of_affine_approximation` |

The modules `NeutralSolution`, `L1Dependence`, `CriticalPerturbation` and `ZeroExistence` are
copies of the uncompiled drafts

L1ContinuousGronwall,L1ContinuousDependence,CriticalPerturbationIdentity,ZeroExistence}.lean`
(with compile fixes); the drafts themselves are unchanged and must not be imported together
with this layer (same declaration names).

Deviations from the scoping signatures (§5 of the scoping note):
* O1 `exists_dirichlet_neutral` adds the conjunct that the normalized solution is positive on
  `(-N, N)`; its proof replaces min--max and spectral counting by Sturm comparison.
* O2 `tendsto_critical_cauchy` takes the cone as `criticalSpeedCone κ`, which is literally the
  set `{c | κ ‖c - a_*‖ ≤ (c - a_*).im ∧ 0 < (c - a_*).im}` of the scoping signature.
* O3: the scoping signature (no smallness hypothesis, no exponential factor) is false for
  `β → ∞`; the compiled versions carry the factor `e^P`, or assume `P ≤ 1`.
-/
