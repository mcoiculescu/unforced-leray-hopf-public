import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-!
# The manuscript's concrete unit-amplitude Gaussian planar vortex

The plane is the ordinary real product space. The differential operators
below use classical one-variable partial derivatives in Cartesian coordinates;
there are no assumed Euler or vorticity identities in the definitions.
-/

noncomputable section
open scoped ContDiff
namespace UnforcedLeray.GaussianVortex

abbrev Plane := ℝ × ℝ

def radiusSq (z : Plane) : ℝ := z.1 ^ 2 + z.2 ^ 2

def planarGaussian (z : Plane) : ℝ := Real.exp (-(radiusSq z / 4))

def streamfunction (z : Plane) : ℝ := -2 * planarGaussian z

def velocity (z : Plane) : Plane :=
  (-z.2 * planarGaussian z, z.1 * planarGaussian z)

def pressure (z : Plane) : ℝ := -Real.exp (-(radiusSq z / 2))

def vorticity (z : Plane) : ℝ := (2 - radiusSq z / 2) * planarGaussian z

/-- The actual classical first Cartesian partial derivative. -/
def partialX (f : Plane → ℝ) (z : Plane) : ℝ :=
  deriv (fun x : ℝ => f (x, z.2)) z.1

/-- The actual classical second Cartesian partial derivative. -/
def partialY (f : Plane → ℝ) (z : Plane) : ℝ :=
  deriv (fun y : ℝ => f (z.1, y)) z.2

def gradient (f : Plane → ℝ) (z : Plane) : Plane :=
  (partialX f z, partialY f z)

def perpendicularGradient (f : Plane → ℝ) (z : Plane) : Plane :=
  (-partialY f z, partialX f z)

def divergence (u : Plane → Plane) (z : Plane) : ℝ :=
  partialX (fun w => (u w).1) z + partialY (fun w => (u w).2) z

def curl (u : Plane → Plane) (z : Plane) : ℝ :=
  partialX (fun w => (u w).2) z - partialY (fun w => (u w).1) z

def scalarAdvection (u : Plane → Plane) (f : Plane → ℝ) (z : Plane) : ℝ :=
  (u z).1 * partialX f z + (u z).2 * partialY f z

def advection (u : Plane → Plane) (z : Plane) : Plane :=
  (scalarAdvection u (fun w => (u w).1) z,
   scalarAdvection u (fun w => (u w).2) z)

theorem contDiff_radiusSq : ContDiff ℝ ∞ radiusSq := by
  unfold radiusSq
  fun_prop

theorem contDiff_planarGaussian : ContDiff ℝ ∞ planarGaussian := by
  unfold planarGaussian radiusSq
  fun_prop

theorem contDiff_streamfunction : ContDiff ℝ ∞ streamfunction := by
  exact contDiff_const.mul contDiff_planarGaussian

theorem contDiff_velocity : ContDiff ℝ ∞ velocity := by
  unfold velocity planarGaussian radiusSq
  fun_prop

theorem contDiff_pressure : ContDiff ℝ ∞ pressure := by
  unfold pressure radiusSq
  fun_prop

theorem contDiff_vorticity : ContDiff ℝ ∞ vorticity := by
  unfold vorticity planarGaussian radiusSq
  fun_prop

end UnforcedLeray.GaussianVortex
