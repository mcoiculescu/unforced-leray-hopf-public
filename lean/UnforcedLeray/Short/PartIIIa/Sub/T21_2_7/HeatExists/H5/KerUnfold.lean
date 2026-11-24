import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_8_5_1_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_8_5_1_1.Int

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/5/1/1`: unfolding the periodic lift against a test

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836.
`AdjKerUnfold m` from the absolute integrability (`adjKerUnfold_int`, weighted Cauchy-Schwarz)
and the Fubini / substitution / periodic-translation computation
(`adjKerUnfold_of_integrable`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjKerUnfold (m : ℝ) (_hm : 8 < m) : AdjKerUnfold m := by
  intro c hc k hk M hY w ψ hψ
  have h := adjKerUnfold_of_integrable hc hk (Lp.stronglyMeasurable w) hψ
    (adjKerUnfold_int hc hk hY w hψ)
  exact h

end UnforcedLeray.Short.IIIa
