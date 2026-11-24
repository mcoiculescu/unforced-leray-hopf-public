import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.XGInt

/-!
# Part II-b, task `PartII-b:G4/2/2/3/1`: `smoothA`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: `F r = ∫₀^r s³ q` has derivative `r³ q r` on `(0,∞)` (`integral_hasDerivAt_right`,
integrability from `xGInt`), and `r³ q` is smooth there, so `F` is smooth on `(0,∞)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

theorem smoothA : UnforcedLeray.Short.IIb.SmoothA := by
  intro q hqG hq
  have hcont : ContinuousOn q (Ioi 0) := hq.continuousOn
  have hfc : ContinuousOn (fun s : ℝ => (s : ℂ) ^ 3 * q s) (Ioi 0) :=
    ContinuousOn.mul (Complex.continuous_ofReal.pow 3).continuousOn hcont
  have hfI : IntegrableOn (fun s : ℝ => (s : ℂ) ^ 3 * q s) (Ioi 0) := (xGInt q hqG).1
  have hderiv : ∀ r : ℝ, 0 < r →
      HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, (s : ℂ) ^ 3 * q s) ((r : ℂ) ^ 3 * q r) r := by
    intro r hr
    have hII : IntervalIntegrable (fun s : ℝ => (s : ℂ) ^ 3 * q s) volume 0 r := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le]
      exact hfI.mono_set Ioc_subset_Ioi_self
    have hmeas : StronglyMeasurableAtFilter (fun s : ℝ => (s : ℂ) ^ 3 * q s) (𝓝 r) :=
      hfc.stronglyMeasurableAtFilter isOpen_Ioi r hr
    exact intervalIntegral.integral_hasDerivAt_right hII hmeas
      (hfc.continuousAt (Ioi_mem_nhds hr))
  have hDiff : DifferentiableOn ℝ (fun r : ℝ => ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s) (Ioi 0) :=
    fun r hr => (hderiv r hr).differentiableAt.differentiableWithinAt
  have hdereq : EqOn (deriv (fun r : ℝ => ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s))
      (fun r : ℝ => (r : ℂ) ^ 3 * q r) (Ioi 0) :=
    fun r hr => (hderiv r hr).deriv
  have hsmooth : ContDiffOn ℝ ∞ (fun r : ℝ => (r : ℂ) ^ 3 * q r) (Ioi 0) := by
    refine ContDiffOn.mul ?_ hq
    exact (Complex.ofRealCLM.contDiff.pow 3).contDiffOn
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
  exact ⟨hDiff, hsmooth.congr hdereq⟩

end UnforcedLeray.Short.IIb

end
