import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalNormalizedCoefficient
import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalNormalizedScalarGauge

/-!
# Exact clamped-clock representation of the normalized free propagator

On a finite active turnover block, the actual normalized free propagator is the scalar integrating
factor times the clamped Gaussian diffusion family.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0123

/-- The gauged free propagator is exactly the scalar exponential times the diffusion clock whose
coefficient is the globally bounded active-block representative. -/
theorem normalizedTurnoverFree_eq_scalar_clampedDiffusion
    {lam κ : ℂ} {R b₀ s t : ℝ} (hb₀ : 0 < b₀) (hR : b₀ ≤ R)
    (hs : 0 ≤ s) (hst : s ≤ t) (htt : t ≤ R - b₀) :
    normalizedTurnoverFree lam κ R t s =
      Complex.exp (-lam * (t - s) - κ * (∫ u in s..t, (R - u)⁻¹)) •
        freeDiffusion (turnoverBlockBeta R b₀) t s := by
  have hclock := normalizedTurnoverFree_eq_gauge_clock (lam := lam) (κ := κ) hb₀ hs hst htt
  have hβ : (∫ u in s..t, turnoverBlockBeta R b₀ u) =
      ∫ u in s..t, (R - u)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hst] at hu
    simpa only [one_div] using
      turnoverBlockBeta_eq_reciprocal hR (hs.trans hu.1) (hu.2.trans htt)
  rw [hclock, freeDiffusion, hβ, gaugeRatio_eq_scalarExp_turnover hb₀ hs hst htt]

end UnforcedLeray.Cons.G3b
