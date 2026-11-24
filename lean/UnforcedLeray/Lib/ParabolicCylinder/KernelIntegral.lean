import UnforcedLeray.Infra.VolterraEvolution.Kernel

/-!
# Time integral for the cylinder heat smoothing kernel

The spatial cylinder estimate has singular factor `ν^(-1/2) (t-r)^(-1/2)`. This is its exact
integral over a finite age interval, using the already proved square-root Volterra kernel identity.
It is the scalar bound needed when the concrete heat-divergence estimate is inserted into the
Navier–Stokes mild formula.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open intervalIntegral

namespace UnforcedLeray.ParabolicCylinder

/-- Exact integral of the viscosity-scaled square-root kernel on a finite interval. -/
theorem integral_viscosity_sqrt_kernel {ν s t : ℝ} (_hν : 0 < ν) :
    ∫ r in s..t, ν ^ (-(1 / 2 : ℝ)) * (t - r) ^ (-(1 / 2 : ℝ)) =
      2 * ν ^ (-(1 / 2 : ℝ)) * (t - s) ^ (1 / 2 : ℝ) := by
  rw [intervalIntegral.integral_const_mul,
    UnforcedLeray.Infra.VolterraEvolution.integral_kernel]
  ring

/-- Exact time integral of the `L²` heat-divergence smoothing profile after inserting viscosity.
The prefactor `2 / √π` is the planar Gaussian-gradient mass constant from
`HeatCylinder.heatDiv_L2_smoothing`; the resulting Duhamel factor is
`4 / √π · ν^(-1/2) · (t-s)^(1/2)`. -/
theorem integral_heatDiv_smoothing_factor {ν s t : ℝ} (hν : 0 < ν) :
    ∫ r in s..t, (2 / Real.sqrt Real.pi) *
        (ν ^ (-(1 / 2 : ℝ)) * (t - r) ^ (-(1 / 2 : ℝ))) =
      (4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) *
        (t - s) ^ (1 / 2 : ℝ) := by
  calc
    _ = (2 / Real.sqrt Real.pi) *
        ∫ r in s..t, ν ^ (-(1 / 2 : ℝ)) * (t - r) ^ (-(1 / 2 : ℝ)) := by
          rw [intervalIntegral.integral_const_mul]
    _ = (2 / Real.sqrt Real.pi) *
        (2 * ν ^ (-(1 / 2 : ℝ)) * (t - s) ^ (1 / 2 : ℝ)) := by
          rw [integral_viscosity_sqrt_kernel hν]
    _ = _ := by ring

end UnforcedLeray.ParabolicCylinder
