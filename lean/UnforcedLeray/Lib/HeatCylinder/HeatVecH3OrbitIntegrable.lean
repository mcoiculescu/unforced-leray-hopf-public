import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ViscousOrbitReal

/-!
# Bochner integrability of actual viscosity-scaled H³ heat paths

A continuous orbit is Bochner integrable on every compact time interval, including intervals
that meet the age-zero join.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.Train (Vec)

/-- The actual viscosity-scaled H³ heat orbit is Bochner integrable on every compact interval. -/
theorem integrableOn_heatVecH3Semigroup_viscousOrbit_Icc {c ν a b : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    IntegrableOn
      (fun t : ℝ => heatVecH3Semigroup (c := c) (θ := ν * t) hc x)
      (Set.Icc a b) := by
  exact (continuous_heatVecH3Semigroup_viscousOrbit hc x).continuousOn.integrableOn_compact
    isCompact_Icc

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.integrableOn_heatVecH3Semigroup_viscousOrbit_Icc
