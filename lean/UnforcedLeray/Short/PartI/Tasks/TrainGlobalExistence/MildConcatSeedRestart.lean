import UnforcedLeray.Short.PartI.Sub.PartI_T04_1
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3SemigroupP0
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Semigroup
import UnforcedLeray.Lib.TrainB.P0ArbitraryInitialLocalMild

/-!
# Part I, task `PartI:T04/1/1`: the seed restart identity

Source: `the November 2 reference manuscript` lines 270-277 (restart).

For `0 ≤ T₁ ≤ t`, the projected heat seed restarts from its value at `T₁` by the heat semigroup:
`P₀ e^{ν t Δ} x = e^{ν(t-T₁)Δ} (P₀ e^{ν T₁ Δ} x)`.  Route: the heat family commutes with `P₀`
(`heatVecH3Semigroup_P0H3CLM_comm`), the semigroup law at nonnegative ages
(`heatVecH3Semigroup_comp_of_nonneg`), and `max 0 (ν s) = ν s` for `s ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-- **Seed restart** (`ConcatSeedRestart`, line 276, "restart"): for `0 ≤ T₁ ≤ t`,
`projectedHeatSeedPath x t = e^{ν(t-T₁)Δ}(projectedHeatSeedPath x T₁)`. -/
theorem concatSeedRestart : ConcatSeedRestart := by
  intro c ν T₁ t hc hν x hT₁ hT₁t
  have hage1 : 0 ≤ ν * (t - T₁) := mul_nonneg hν.le (by linarith)
  have hage2 : 0 ≤ ν * T₁ := mul_nonneg hν.le hT₁
  have hνt : 0 ≤ ν * t := mul_nonneg hν.le (by linarith)
  have hsum : ν * (t - T₁) + ν * T₁ = ν * t := by ring
  have hcomp : heatVecH3Semigroup (c := c) (θ := ν * (t - T₁)) hc
      (heatVecH3Semigroup (c := c) (θ := ν * T₁) hc x) =
      heatVecH3Semigroup (c := c) (θ := ν * t) hc x := by
    rw [← hsum, ← heatVecH3Semigroup_comp_of_nonneg hc hage1 hage2,
      ContinuousLinearMap.comp_apply]
  change P0H3CLM hc (heatVecH3Semigroup (c := c) (θ := max 0 (ν * t)) hc x) =
    heatVecH3Semigroup (c := c) (θ := ν * (t - T₁)) hc
      (P0H3CLM hc (heatVecH3Semigroup (c := c) (θ := max 0 (ν * T₁)) hc x))
  rw [← heatVecH3Semigroup_P0H3CLM_comm hc, max_eq_right hνt, max_eq_right hage2, hcomp]

end UnforcedLeray.Short.PartI
