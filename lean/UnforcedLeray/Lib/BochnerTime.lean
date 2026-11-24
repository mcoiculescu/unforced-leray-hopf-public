import UnforcedLeray.Lib.BochnerTime.Prelim
import UnforcedLeray.Lib.BochnerTime.Basic
import UnforcedLeray.Lib.BochnerTime.Energy
import UnforcedLeray.Lib.BochnerTime.Trace
import UnforcedLeray.Lib.BochnerTime.Separating
import UnforcedLeray.Lib.BochnerTime.JointRep
import UnforcedLeray.Lib.BochnerTime.Slices
import UnforcedLeray.Lib.BochnerTime.Duhamel
import UnforcedLeray.Lib.BochnerTime.Periodic
import UnforcedLeray.Lib.BochnerTime.Translation
import UnforcedLeray.Lib.BochnerTime.MixedNorm

/-!
# Bochner functions of time (Wave 1, block 1D part 2: INF14 targets T1–T5, T7, T9)

Main file of the INF14 layer of the Lean build plan

proposed signatures in `scoping/INF11-INF14-Sobolev.md` §5.2). Namespace
`UnforcedLeray.BochnerTime`. Decisions used: D2 (phase space; INF14 T9 supplies only the
averaging identity), D9 (Lions–Magenes, INF14 T8, is not built), D15 (the Banach-valued FTC and
the Hilbert energy identity are built once, here).

| Target | Module | Main declarations |
|---|---|---|
| T1 | `Prelim`, `Basic` | `HasWeakDerivTime`, `HasWeakDerivTime.exists_rep`, `.rep`, `.continuousOn_rep`, `.ae_eq_rep`, `.rep_sub_rep`, `.eqOn_rep`, `.rep_eq`, `hasWeakDerivTime_of_primitive`, `.hasDerivAt_rep`, `.contDiffOn_rep`, `.map`, `.congr_ae`, `.add`, `.const_smul`; tools `absolutelyContinuousOnInterval_primitive`, `integral_deriv_smul_primitive`, `ae_eq_const_of_integral_deriv_smul_eq_zero` (du Bois-Reymond) |
| T2 | `Energy` | `integral_eq_sub_of_ae_hasDerivAt`, `.ae_hasDerivAt_rep`, `.norm_rep_sub_le`, `.abs_norm_rep_sub_norm_rep_le`, `.sup_le_avg`, `.norm_sq_sub`, `.norm_sq_sub'`, `.weighted_norm_sq_sub` |
| T3 | `Trace` | `trace_interp` (B0236, tex 4059–4065), `traceConst`, `.abs_rep_le_of_le`, `integral_abs_le_of_memLp`; the B0445 pairing is `HasWeakDerivTime.map` |
| T4 | `Separating` | `hasWeakDerivTime_of_separating`, `hasWeakDerivTime_of_dual` |
| T5 | `JointRep`, `Slices` | `exists_isJointRep_of_continuousOn`, `exists_measurable_isJointRep_of_continuousOn`, `jointRep_ae_eq_prod` (reusing the drafted `Infra/JointMeasurableRep`); `toPathLq`, `toPathLq_congr_ae`, `stronglyMeasurable_toPathLq`, `stronglyMeasurable_toPath_Lq` (product `L^q` → `L^q`-valued slices, with the norm identity) |
| T7 | `Duhamel` | `stronglyMeasurable_apply`, `aestronglyMeasurable_apply`, `continuousOn_duhamel` |
| T9 | `Periodic`, `Translation`, `MixedNorm` | `lintegral_Ioc_comp_add_right`, `lintegral_center_average` (B0425, eq. `(free-stress-16)`, tex 7519–7524), `integral_center_average`; `continuous_translate_real`, `continuous_translate_addCircle`, `translate_ae_eq` (B0421); `mixedNormLpLinf`, `mixedNormLpLinf_le_of_ae_bound`, `mixedNormLpLinf_mono` (B0778) |
-/
