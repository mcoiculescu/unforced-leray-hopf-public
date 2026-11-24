import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Physical ring chart

These are the manuscript's exact radial similarity coordinates on `r > 0`,
with ring scale `R > 0`: `a = R/r`, `q = R log(r/R)`, `η = az`, and `s = a²t`.
The derivative identities below are ordinary one-variable derivatives and
supply the chain rule factors used in the complete solenoidal lift.
-/

set_option autoImplicit false
noncomputable section
namespace UnforcedLeray.RingLift

def radialScale (R r : ℝ) : ℝ := R / r
def logRadius (R r : ℝ) : ℝ := R * Real.log (r / R)
def transverseCoordinate (R r z : ℝ) : ℝ := radialScale R r * z
def ageCoordinate (R r t : ℝ) : ℝ := (radialScale R r) ^ 2 * t

theorem hasDerivAt_radialScale (R r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (radialScale R) (-radialScale R r / r) r := by
  have he : -radialScale R r / r = R * (-1 / r ^ 2) := by
    dsimp [radialScale]
    field_simp
  rw [he]
  convert (((hasDerivAt_id r).inv hr).const_mul R) using 1 <;>
    rfl

theorem hasDerivAt_logRadius (R r : ℝ) (hR : R ≠ 0) (hr : r ≠ 0) :
    HasDerivAt (logRadius R) (radialScale R r) r := by
  have hratio : r / R ≠ 0 := div_ne_zero hr hR
  have he : radialScale R r = R * ((1 / R) / (r / R)) := by
    dsimp [radialScale]
    field_simp
  rw [he]
  convert ((((hasDerivAt_id r).div_const R).log hratio).const_mul R) using 1 <;>
    rfl

theorem hasDerivAt_transverseCoordinate_radial (R r z : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun x => transverseCoordinate R x z)
      (-transverseCoordinate R r z / r) r := by
  have he : -transverseCoordinate R r z / r =
      (-radialScale R r / r) * z := by
    dsimp [transverseCoordinate]
    ring
  rw [he]
  convert ((hasDerivAt_radialScale R r hr).mul_const z) using 1 <;> rfl

theorem hasDerivAt_ageCoordinate_radial (R r t : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun x => ageCoordinate R x t)
      (-2 * ageCoordinate R r t / r) r := by
  have he : -2 * ageCoordinate R r t / r =
      (2 * radialScale R r * (-radialScale R r / r)) * t := by
    dsimp [ageCoordinate]
    ring
  rw [he]
  convert (((hasDerivAt_radialScale R r hr).pow 2).mul_const t) using 1 <;>
    first | rfl | simp

theorem hasDerivAt_transverseCoordinate_axial (R r z : ℝ) :
    HasDerivAt (transverseCoordinate R r) (radialScale R r) z := by
  convert ((hasDerivAt_id z).const_mul (radialScale R r)) using 1 <;>
    first | rfl | simp

theorem hasDerivAt_ageCoordinate_time (R r t : ℝ) :
    HasDerivAt (ageCoordinate R r) ((radialScale R r) ^ 2) t := by
  convert ((hasDerivAt_id t).const_mul ((radialScale R r) ^ 2)) using 1 <;>
    first | rfl | simp

end UnforcedLeray.RingLift
