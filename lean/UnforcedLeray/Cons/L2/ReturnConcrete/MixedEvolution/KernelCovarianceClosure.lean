import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelBoundedPeriodicCLM

/-!
# Closing heat/response covariance in the normalized-cell `L²` carrier

This lemma records the exact operator-limit step: once actual bounded continuous periodic
representatives are dense in the normalized-cell tensor `L²`, the positive-age covariance
extends to every input by continuity of the actual heat and heat-divergence CLMs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284
open UnforcedLeray.HeatCylinder

/-- The bounded-continuous periodic covariance identity passes to a normalized-cell `L²` limit.
The approximating representatives and quotient values are required to be the same actual fields. -/
theorem heatL2CLM_comp_heatDivL2CLM_of_bddContinuous_limit {c α β : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hβ : 0 < β)
    {x : Lp (Plane × Plane) 2 (cellMeasure c)}
    {xSeq : ℕ → Lp (Plane × Plane) 2 (cellMeasure c)}
    {Tn : ℕ → Plane → Plane × Plane}
    {hn : ∀ n, MemLp (Tn n) 2 (cellMeasure c)}
    (hcont : ∀ n, Continuous (Tn n))
    (hbound : ∀ n, ∃ M : ℝ, ∀ z, ‖Tn n z‖ ≤ M)
    (hper : ∀ n, IsQPeriodic c (Tn n))
    (hrep : ∀ n, xSeq n = (hn n).toLp (Tn n))
    (hlim : Tendsto xSeq atTop (𝓝 x)) :
    heatL2CLM hc α (heatDivL2CLM hc hβ x) =
      heatDivL2CLM hc (add_pos hα hβ) x := by
  have hcov : ∀ n, heatL2CLM hc α (heatDivL2CLM hc hβ (xSeq n)) =
      heatDivL2CLM hc (add_pos hα hβ) (xSeq n) := by
    intro n
    rw [hrep n]
    exact heatL2CLM_comp_heatDivL2CLM_of_bdd_continuous hc hα hβ
      (hcont n) (hbound n) (hper n) (hn n)
  have hdivLim : Tendsto (fun n => heatDivL2CLM hc hβ (xSeq n)) atTop
      (𝓝 (heatDivL2CLM hc hβ x)) :=
    ((heatDivL2CLM hc hβ).continuous.tendsto x).comp hlim
  have hleftLim : Tendsto (fun n =>
      heatL2CLM hc α (heatDivL2CLM hc hβ (xSeq n))) atTop
      (𝓝 (heatL2CLM hc α (heatDivL2CLM hc hβ x))) :=
    ((heatL2CLM hc α).continuous.tendsto _).comp hdivLim
  have hrightLim : Tendsto (fun n => heatDivL2CLM hc (add_pos hα hβ) (xSeq n)) atTop
      (𝓝 (heatDivL2CLM hc (add_pos hα hβ) x)) :=
    ((heatDivL2CLM hc (add_pos hα hβ)).continuous.tendsto _).comp hlim
  have hleft' : Tendsto (fun n => heatDivL2CLM hc (add_pos hα hβ) (xSeq n)) atTop
      (𝓝 (heatL2CLM hc α (heatDivL2CLM hc hβ x))) := by
    apply hleftLim.congr'
    filter_upwards with n
    exact hcov n
  exact tendsto_nhds_unique hleft' hrightLim

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.heatL2CLM_comp_heatDivL2CLM_of_bddContinuous_limit
