import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelPeriodicL2Covariance
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.FluxHeatCLM

/-!
# Covariance on actual weighted flux inputs after normalized-cell realization

The input class is the concrete normalized-cell tensor obtained from two genuine `X c m`
columns. The signed output is the actual `-B0296.heatDiv` CLM used by the physical response.
This result is still stated in the normalized-cell range; the weighted state-space identification
is kept as a separate bridge.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284
open UnforcedLeray.HeatCylinder
open UnforcedLeray.B0579

/-- Positive-age actual normalized-cell covariance for the signed B0296 response to any pair of
weighted flux columns. -/
theorem heatL2CLM_comp_xFluxNegativeHeatDivL2CLM {c m α β : ℝ}
    (hc : 0 < c) (hm : 1 ≤ m) (hα : 0 < α) (hβ : 0 < β)
    (F : Fin 2 → X c m) :
    heatL2CLM hc α (xFluxNegativeHeatDivL2CLM hc hm hβ F) =
      xFluxNegativeHeatDivL2CLM hc hm (add_pos hα hβ) F := by
  change heatL2CLM hc α
      ((-1 : ℝ) • heatDivL2CLM hc hβ (xFluxPeriodicTensorInputCLM hc hm F)) =
    (-1 : ℝ) • heatDivL2CLM hc (add_pos hα hβ)
      (xFluxPeriodicTensorInputCLM hc hm F)
  rw [map_smul]
  rw [heatL2CLM_comp_heatDivL2CLM hc hα hβ (xFluxPeriodicTensorInputCLM hc hm F)]

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.heatL2CLM_comp_xFluxNegativeHeatDivL2CLM
