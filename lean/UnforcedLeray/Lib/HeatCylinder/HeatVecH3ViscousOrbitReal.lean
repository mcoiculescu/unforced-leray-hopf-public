import UnforcedLeray.Lib.HeatCylinder.HeatVecH3OrbitRealContinuity

/-!
# Full real-time continuity of the viscosity-scaled actual H³ heat orbit

The physical nonnegative-time orbit is a composition of the all-age Gaussian orbit with the
actual affine age parameter.
-/

set_option autoImplicit false

noncomputable section

open Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.Train (Vec)

/-- For every real viscosity parameter, the actual H³ heat orbit at age `ν * t` is continuous
on all real times. -/
theorem continuous_heatVecH3Semigroup_viscousOrbit {c ν : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    Continuous (fun t : ℝ => heatVecH3Semigroup (c := c) (θ := ν * t) hc x) := by
  exact (continuous_heatVecH3Semigroup_orbit hc x).comp
    (continuous_const.mul continuous_id)

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.continuous_heatVecH3Semigroup_viscousOrbit
