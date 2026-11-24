import UnforcedLeray.Lib.HeatCylinder.HeatL2SemigroupClosed
import UnforcedLeray.Lib.HeatCylinder.HeatL2OrbitContinuity

/-!
# Positive-time continuous normalized-cell zero-order heat family
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Topology Set

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.B0284 (cellMeasure)
open UnforcedLeray.GaussianVortex (Plane)

/-- The actual normalized-cell heat CLM orbit is continuous on strictly positive ages. -/
theorem continuousOn_heatL2CLM_positive {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) :
    ContinuousOn (fun θ => heatL2CLM hc θ x) (Ioi 0) := by
  intro θ hθ
  simpa only [heatL2CLM_apply] using
    (continuousAt_heatL2_of_pos hc hθ x).continuousWithinAt

/-- The actual heat orbit is strongly measurable on positive ages, by continuity into the
normalized-cell `L²` quotient. -/
theorem aestronglyMeasurable_heatL2CLM_positive {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) :
    AEStronglyMeasurable (fun θ => heatL2CLM hc θ x) (volume.restrict (Ioi 0)) := by
  exact (continuousOn_heatL2CLM_positive hc x).aestronglyMeasurable measurableSet_Ioi

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.continuousOn_heatL2CLM_positive
#print axioms UnforcedLeray.HeatCylinder.aestronglyMeasurable_heatL2CLM_positive
