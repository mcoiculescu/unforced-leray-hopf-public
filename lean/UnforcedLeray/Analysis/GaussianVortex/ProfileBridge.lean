import UnforcedLeray.Analysis.GaussianVortex.PlanarEuler
import UnforcedLeray.Analysis.GaussianVortex.RadialProfile

/-!
# The actual Cartesian Gaussian vortex and its radial profiles

These identities use the ordinary Euclidean radius √(x²+y²). They hold at
the origin as well as away from it, and connect the explicit planar fields
to the radial coefficients in the manuscript's Rayleigh equation.
-/

noncomputable section
namespace UnforcedLeray.GaussianVortex

theorem radiusSq_nonnegative (z : Plane) : 0 ≤ radiusSq z := by
  unfold radiusSq
  positivity

/-- The ordinary Euclidean radius of the Cartesian point. -/
def radialCoordinate (z : Plane) : ℝ := Real.sqrt (radiusSq z)

theorem radialCoordinate_nonnegative (z : Plane) : 0 ≤ radialCoordinate z :=
  Real.sqrt_nonneg _

theorem radialCoordinate_sq (z : Plane) : radialCoordinate z ^ 2 = radiusSq z :=
  Real.sq_sqrt (radiusSq_nonnegative z)

/-- The planar Gaussian is exactly the radial angular velocity at |z|. -/
theorem planarGaussian_eq_radialOmega (z : Plane) :
    planarGaussian z = radialOmega (Real.sqrt (radiusSq z)) := by
  unfold planarGaussian radialOmega
  rw [Real.sq_sqrt (radiusSq_nonnegative z)]

/-- The Cartesian vorticity has exactly the manuscript's radial profile. -/
theorem vorticity_eq_radialVorticity (z : Plane) :
    vorticity z = radialVorticity (Real.sqrt (radiusSq z)) := by
  unfold vorticity radialVorticity
  rw [Real.sq_sqrt (radiusSq_nonnegative z), planarGaussian_eq_radialOmega]

/-- The Cartesian streamfunction agrees with the radial streamfunction. -/
theorem streamfunction_eq_radialStreamfunction (z : Plane) :
    streamfunction z = radialStreamfunction (Real.sqrt (radiusSq z)) := by
  unfold streamfunction radialStreamfunction
  rw [planarGaussian_eq_radialOmega]

/-- The same coefficient drives the Cartesian vorticity gradient and radial Rayleigh equation. -/
theorem radialK_at_planar_radius (z : Plane) :
    radialK (Real.sqrt (radiusSq z)) =
      (radiusSq z / 4 - 2) * planarGaussian z := by
  unfold radialK
  rw [Real.sq_sqrt (radiusSq_nonnegative z), ← planarGaussian_eq_radialOmega]

/-- The actual planar velocity uses exactly the radial angular speed. -/
theorem velocity_eq_radialOmega (z : Plane) :
    velocity z =
      (-z.2 * radialOmega (Real.sqrt (radiusSq z)),
        z.1 * radialOmega (Real.sqrt (radiusSq z))) := by
  unfold velocity
  rw [planarGaussian_eq_radialOmega]

/-- The radial curl formula and Cartesian vorticity agree everywhere. -/
theorem vorticity_eq_radial_curl (z : Plane) :
    vorticity z = 2 * radialOmega (radialCoordinate z) +
      radialCoordinate z * deriv radialOmega (radialCoordinate z) := by
  rw [vorticity_eq_radialVorticity]
  exact radialVorticity_eq_radial_curl _

/-- The actual Cartesian vorticity gradient uses the exact radial Rayleigh coefficient. -/
theorem gradient_vorticity_eq_radialK (z : Plane) :
    gradient vorticity z = radialK (Real.sqrt (radiusSq z)) • z := by
  apply Prod.ext
  · change partialX vorticity z = radialK (Real.sqrt (radiusSq z)) * z.1
    rw [partialX_vorticity, radialK_at_planar_radius]
    ring
  · change partialY vorticity z = radialK (Real.sqrt (radiusSq z)) * z.2
    rw [partialY_vorticity, radialK_at_planar_radius]
    ring

end UnforcedLeray.GaussianVortex
