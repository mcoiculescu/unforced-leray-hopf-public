import UnforcedLeray.Analysis.Rayleigh.RealSpeed.Defs
import UnforcedLeray.Analysis.Sturm.NeutralEigenIdentity

/-!
# Real-speed Rayleigh energy from actual H² data

The undivided Gaussian Rayleigh equation supplies the weighted-potential
integrability, including at critical points. Whole-line integration by parts
then gives the negative energy identity without a boundary-term assumption.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace UnforcedLeray.Rayleigh.RealSpeed
open Sturm

/-- The weighted potential equals an integrable differential expression.
At a critical point both sides vanish by the explicit trace hypothesis. -/
theorem potential_mul_sq_eq_second_mul_sub {c : ℝ} {f : ℝ → ℝ}
    (heq : ∀ t, (neutralOmega t - c) * (deriv (deriv f) t - 4 * f t) -
      gaussianRayleighCoefficient t * f t = 0)
    (htrace : ∀ t, neutralOmega t = c → f t = 0) (t : ℝ) :
    speedPotential c t * f t ^ 2 = deriv (deriv f) t * f t - 3 * f t ^ 2 := by
  by_cases hd : neutralOmega t - c = 0
  · have hf0 := htrace t (sub_eq_zero.mp hd)
    simp [hf0]
  · have hquot : gaussianRayleighCoefficient t / (neutralOmega t - c) * f t =
        deriv (deriv f) t - 4 * f t := by
      rw [div_mul_eq_mul_div]
      apply (div_eq_iff hd).mpr
      rw [mul_comm (deriv (deriv f) t - 4 * f t)]
      exact (sub_eq_zero.mp (heq t)).symm
    unfold speedPotential
    calc
      (1 + gaussianRayleighCoefficient t / (neutralOmega t - c)) * f t ^ 2 =
          f t ^ 2 + (gaussianRayleighCoefficient t / (neutralOmega t - c) * f t) *
            f t := by ring
      _ = deriv (deriv f) t * f t - 3 * f t ^ 2 := by rw [hquot]; ring

/-- The equation derives potential integrability solely from the genuine L²
value and second derivative; it is not a premise of the energy theorem. -/
theorem integrable_potential_mul_sq {c : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hddf : MemLp (deriv (deriv f)) 2 volume)
    (heq : ∀ t, (neutralOmega t - c) * (deriv (deriv f) t - 4 * f t) -
      gaussianRayleighCoefficient t * f t = 0)
    (htrace : ∀ t, neutralOmega t = c → f t = 0) :
    Integrable (fun t => speedPotential c t * f t ^ 2) := by
  have hm : Integrable (fun t => f t ^ 2) := by
    exact hf.integrable_sq
  have hd : Integrable (fun t => deriv (deriv f) t * f t) :=
    hddf.integrable_mul hf
  have hident : (fun t => speedPotential c t * f t ^ 2) =
      (fun t => deriv (deriv f) t * f t - 3 * f t ^ 2) :=
    funext (potential_mul_sq_eq_second_mul_sub heq htrace)
  rw [hident]
  exact hd.sub (hm.const_mul 3)

/-- The whole-line real-speed comparison energy is exactly minus three times
the mass, using the actual Gaussian ODE and actual H² integration by parts. -/
theorem real_speed_energy_eq_neg_three_mass {c : ℝ} {f : ℝ → ℝ}
    (hfc : ContDiff ℝ 2 f)
    (hf : MemLp f 2 volume) (hdf : MemLp (deriv f) 2 volume)
    (hddf : MemLp (deriv (deriv f)) 2 volume)
    (heq : ∀ t, (neutralOmega t - c) * (deriv (deriv f) t - 4 * f t) -
      gaussianRayleighCoefficient t * f t = 0)
    (htrace : ∀ t, neutralOmega t = c → f t = 0) :
    (∫ t, deriv f t ^ 2 + speedPotential c t * f t ^ 2) =
      -3 * (∫ t, f t ^ 2) := by
  have hm : Integrable (fun t => f t ^ 2) := by
    exact hf.integrable_sq
  have hd : Integrable (fun t => deriv f t ^ 2) := by
    exact hdf.integrable_sq
  have hdd : Integrable (fun t => deriv (deriv f) t * f t) :=
    hddf.integrable_mul hf
  have hv := integrable_potential_mul_sq hf hddf heq htrace
  have hip : (∫ t, deriv (deriv f) t * f t) = -(∫ t, deriv f t ^ 2) := by
    simpa only [pow_two] using integral_second_mul_eq_neg_first_mul
      hfc (hfc.of_le (by norm_num)) hdf hddf hf hdf
  have hpotential : (∫ t, speedPotential c t * f t ^ 2) =
      (∫ t, deriv (deriv f) t * f t) - 3 * (∫ t, f t ^ 2) := by
    calc
      (∫ t, speedPotential c t * f t ^ 2) =
          ∫ t, deriv (deriv f) t * f t - 3 * f t ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall
          (potential_mul_sq_eq_second_mul_sub heq htrace))
      _ = (∫ t, deriv (deriv f) t * f t) - 3 * (∫ t, f t ^ 2) := by
        rw [integral_sub hdd (hm.const_mul 3), integral_const_mul]
  rw [integral_add hd hv, hpotential, hip]
  ring

end UnforcedLeray.Rayleigh.RealSpeed
