import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_5_1_1
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_5.HarmonicPeriodic.SummDiff.Core

/-!
# Part III-a, `PartIII-a:T23/5/1/1/1`: `HarmSummDiff` (source 2354-2356)

Summability of the terms `(u_k - iη)⁻²` and differentiability of the periodized quadrupole at
points with `η ≠ 0`. The analytic work is in `SummDiff/Core.lean`
(`hc_hasFDerivAt_harmPeriodic`, `hc_summable_harmTerm`).
-/

set_option autoImplicit false

noncomputable section

theorem harmSummDiff : UnforcedLeray.Short.IIIa.HarmSummDiff := by
  intro c hc y hy
  exact ⟨UnforcedLeray.Short.IIIa.hc_summable_harmTerm c hc y hy,
    (UnforcedLeray.Short.IIIa.hc_hasFDerivAt_harmPeriodic c hc y hy).differentiableAt⟩
