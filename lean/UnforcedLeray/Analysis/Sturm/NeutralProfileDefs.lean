import UnforcedLeray.GaussianPotentialSup
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! The explicit Gaussian angular velocity and its neutral comparison profile. -/
noncomputable section
open scoped ContDiff
namespace UnforcedLeray.Sturm
/-- The square-radius coordinate x=r²/4 in logarithmic radius. -/
def neutralRadius (t : ℝ) : ℝ := Real.exp (2 * t) / 4

/-- The actual Gaussian angular velocity. -/
def neutralOmega (t : ℝ) : ℝ := Real.exp (-neutralRadius t)

/-- The critical log-radius at which the angular speed is e⁻². -/
def neutralCriticalTime : ℝ := Real.log 8 / 2

/-- The explicit neutral comparison solution. -/
def neutralProfile (t : ℝ) : ℝ :=
  Real.exp t * (neutralOmega t - Real.exp (-2))

theorem neutralRadius_pos (t : ℝ) : 0 < neutralRadius t := by
  unfold neutralRadius
  positivity

theorem neutralProfile_smooth : ContDiff ℝ ∞ neutralProfile := by
  unfold neutralProfile neutralOmega neutralRadius
  fun_prop

theorem continuous_neutralRadius : Continuous neutralRadius := by
  unfold neutralRadius
  fun_prop

theorem continuous_neutralOmega : Continuous neutralOmega := by
  unfold neutralOmega
  exact Real.continuous_exp.comp continuous_neutralRadius.neg

end UnforcedLeray.Sturm
