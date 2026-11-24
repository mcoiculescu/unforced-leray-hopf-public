import UnforcedLeray.Analysis.Rayleigh.SpeedBound

/-! Explicit Gaussian comparison profiles for arbitrary real Rayleigh speeds. -/
noncomputable section
namespace UnforcedLeray.Rayleigh.RealSpeed
open Sturm

/-- The actual comparison function h_c(t)=exp(t)(Ω(t)−c). -/
def speedProfile (c t : ℝ) : ℝ := Real.exp t * (neutralOmega t - c)

/-- The real comparison potential, used away from a critical point and in weighted forms. -/
def speedPotential (c t : ℝ) : ℝ :=
  1 + gaussianRayleighCoefficient t / (neutralOmega t - c)

/-- The explicit critical radius in logarithmic coordinates, used for 0<c<1. -/
def criticalTime (c : ℝ) : ℝ := Real.log (-4 * Real.log c) / 2

end UnforcedLeray.Rayleigh.RealSpeed
