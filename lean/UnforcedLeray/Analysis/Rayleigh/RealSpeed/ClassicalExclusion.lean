import UnforcedLeray.Analysis.Rayleigh.RealSpeed.Energy
import UnforcedLeray.Analysis.Rayleigh.RealSpeed.Profile
import UnforcedLeray.Analysis.Rayleigh.RealSpeed.CriticalPoint
import UnforcedLeray.Analysis.Rayleigh.RealSpeed.WeightedGroundState
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Exclusion of nonneutral real speeds for actual classical H² modes

The Gaussian equation forces zero trace at any critical point. Its explicit
comparison profile has at most one zero. Actual weighted ground-state
positivity, with product integrability derived from the same equation, then
contradicts the negative energy identity unless the mode vanishes.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace UnforcedLeray.Rayleigh.RealSpeed
open Sturm GaussianPotential

/-- The totalized real potential is measurable, even at its possible singular point. -/
theorem measurable_speedPotential (c : ℝ) : Measurable (speedPotential c) := by
  unfold speedPotential gaussianRayleighCoefficient
  exact measurable_const.add
    ((measurable_Wlog.neg.mul continuous_gaussianOffset.measurable).div
      (continuous_neutralOmega.measurable.sub measurable_const))

/-- Every real C² H² Gaussian mode at a nonneutral real speed is zero.
The equation is the actual undivided Rayleigh equation; neither weighted
integrability nor a ground-state inequality is assumed. -/
theorem classical_real_mode_eq_zero_of_ne_critical {c : ℝ} {f : ℝ → ℝ}
    (hc : c ≠ gaussianCriticalSpeed) (hfc : ContDiff ℝ 2 f)
    (hf : MemLp f 2 volume) (hdf : MemLp (deriv f) 2 volume)
    (hddf : MemLp (deriv (deriv f)) 2 volume)
    (heq : ∀ t, (neutralOmega t - c) * (deriv (deriv f) t - 4 * f t) -
      gaussianRayleighCoefficient t * f t = 0) : f = 0 := by
  have htrace : ∀ t, neutralOmega t = c → f t = 0 := by
    intro t ht
    apply real_value_zero_at_critical (n := 2) ht hc
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using heq t
  have hpot := integrable_potential_mul_sq hf hddf heq htrace
  have hode : ∀ t, speedProfile c t ≠ 0 →
      deriv (deriv (speedProfile c)) t = speedPotential c t * speedProfile c t := by
    intro t ht
    exact speedProfile_ode_potential ((speedProfile_ne_zero_iff c t).mp ht)
  have hnonneg : 0 ≤ ∫ t, deriv f t ^ 2 + speedPotential c t * f t ^ 2 := by
    by_cases hcrit : ∃ a, neutralOmega a = c
    · obtain ⟨a, ha⟩ := hcrit
      exact weighted_groundState_nonneg_trace_zero
        (speedProfile_smooth c) (hfc.of_le (by norm_num)) hf hdf
        (htrace a ha) (fun t ht => speedProfile_ne_zero_off ha ht) hode
        (measurable_speedPotential c) hpot
    · exact weighted_groundState_nonneg
        (speedProfile_smooth c) (hfc.of_le (by norm_num)) hf hdf
        (speedProfile_ne_zero_of_not_exists hcrit) hode
        (measurable_speedPotential c) hpot
  have henergy := real_speed_energy_eq_neg_three_mass hfc hf hdf hddf heq htrace
  have hmass : (∫ t, f t ^ 2) = 0 := by
    have hm : 0 ≤ ∫ t, f t ^ 2 := integral_nonneg (fun t => sq_nonneg (f t))
    rw [henergy] at hnonneg
    linarith
  have hsq := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg (f t))
    hf.integrable_sq).mp hmass
  have hae : f =ᵐ[volume] 0 := by
    filter_upwards [hsq] with t ht
    simpa only [Pi.zero_apply, sq_eq_zero_iff] using ht
  exact MeasureTheory.Measure.eq_of_ae_eq hae hfc.continuous continuous_zero

end UnforcedLeray.Rayleigh.RealSpeed
