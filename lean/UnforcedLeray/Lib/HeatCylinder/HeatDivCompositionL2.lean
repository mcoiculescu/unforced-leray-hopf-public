import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelBoundedPeriodicCLM
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelPeriodicL2Density

/-!
# Actual heat after heat-divergence on normalized-cell `L²`

The positive-age covariance is assembled here from the already-proved bounded-continuous periodic
identity and the actual smooth periodic density theorem. The Gaussian kernel/Fubini calculation is
reused from its lower-level lemmas; this leaf does not import the Return composition theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- The actual normalized-cell Gaussian heat after actual B0296 heat-divergence is the same
positive-age heat-divergence at the summed age, for every tensor `L²` class. -/
theorem heatL2CLM_comp_heatDivL2CLM {c α β : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hβ : 0 < β)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) :
    heatL2CLM hc α (heatDivL2CLM hc hβ x) =
      heatDivL2CLM hc (add_pos hα hβ) x := by
  obtain ⟨xSeq, Tn, hn, hcont, hbound, hper, hrep, hlim⟩ :=
    exists_bddContinuous_periodic_kernelTensor_approx hc x
  exact heatL2CLM_comp_heatDivL2CLM_of_bddContinuous_limit
    hc hα hβ hcont hbound hper hrep hlim

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatL2CLM_comp_heatDivL2CLM
