import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelCovarianceClosure
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelPeriodicL2Density

/-!
# Positive-age covariance for every normalized-cell periodic tensor class

The actual smooth-cylinder approximants supplied by `KernelPeriodicL2Density` close the
normalized-cell operator-limit argument without an additional density premise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284
open UnforcedLeray.HeatCylinder

/-- Actual normalized-cell heat and signed heat-divergence covariance at positive ages, for
arbitrary normalized-cell tensor L² data. The approximating periodic representatives are the
literal images of compact-axial smooth cylinder tensors constructed from the input class. -/
theorem heatL2CLM_comp_heatDivL2CLM {c α β : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hβ : 0 < β)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) :
    heatL2CLM hc α (heatDivL2CLM hc hβ x) =
      heatDivL2CLM hc (add_pos hα hβ) x := by
  obtain ⟨xSeq, Tn, hn, hcont, hbound, hper, hrep, hlim⟩ :=
    exists_bddContinuous_periodic_kernelTensor_approx hc x
  exact heatL2CLM_comp_heatDivL2CLM_of_bddContinuous_limit
    hc hα hβ hcont hbound hper hrep hlim

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.heatL2CLM_comp_heatDivL2CLM
