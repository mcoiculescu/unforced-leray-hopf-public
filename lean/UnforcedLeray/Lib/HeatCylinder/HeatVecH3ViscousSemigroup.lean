import UnforcedLeray.Lib.HeatCylinder.HeatVecH3OrbitIntegrable

/-!
# The actual viscosity-scaled centered H³ heat semigroup

The nonnegative-age semigroup law transports through the physical age map `t ↦ ν t`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.Train (Vec)

/-- At nonnegative times and viscosity, the actual H³ heat family at age `ν t` obeys the
semigroup composition law with physical time addition. -/
theorem heatVecH3Semigroup_viscous_comp_of_nonneg {c ν s t : ℝ} (hc : 0 < c)
    (hν : 0 ≤ ν) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (heatVecH3Semigroup (c := c) (θ := ν * s) hc).comp
      (heatVecH3Semigroup (c := c) (θ := ν * t) hc) =
      heatVecH3Semigroup (c := c) (θ := ν * (s + t)) hc := by
  simpa only [mul_add] using
    (heatVecH3Semigroup_comp_of_nonneg hc (mul_nonneg hν hs) (mul_nonneg hν ht))

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatVecH3Semigroup_viscous_comp_of_nonneg
