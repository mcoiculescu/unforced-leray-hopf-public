import UnforcedLeray.Analysis.Rayleigh.GaussianMode

/-!
# A direct uniform bound on unstable Gaussian annular speeds

The actual energy identities give |c-a*|≤1 without invoking a separate
semicircle theorem. This is enough for compact extraction of spectral speeds.
It does not claim the sharper Howard disk or a sign for the real part of c.
-/
noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Rayleigh
open GaussianPotential Sturm

theorem gaussianCriticalSpeed_pos : 0 < gaussianCriticalSpeed := Real.exp_pos _
theorem gaussianCriticalSpeed_lt_one : gaussianCriticalSpeed < 1 :=
  Real.exp_lt_one_iff.mpr (by norm_num)

theorem neutralOmega_pos (t : ℝ) : 0 < neutralOmega t := Real.exp_pos _
theorem neutralOmega_lt_one (t : ℝ) : neutralOmega t < 1 := by
  apply Real.exp_lt_one_iff.mpr
  exact neg_neg_of_pos (neutralRadius_pos t)

theorem gaussianOffset_sq_le_one (t : ℝ) : gaussianOffset t ^ 2 ≤ 1 := by
  have hO := neutralOmega_pos t
  have hO' := neutralOmega_lt_one t
  have ha := gaussianCriticalSpeed_pos
  have ha' := gaussianCriticalSpeed_lt_one
  unfold gaussianOffset
  nlinarith [sq_nonneg (neutralOmega t - gaussianCriticalSpeed)]

namespace GaussianAnnularMode
variable {c : ℂ} {F : ℝ → ℂ} {l r : ℝ}
  (h : GaussianAnnularMode c F l r)
include h

theorem energy_le_denominator_mass :
    intervalEnergy F l r ≤
      ∫ t in Ioc l r,
        Wlog t / denominator (gaussianOffset t) (shiftedSpeed c) * ‖F t‖ ^ 2 := by
  rw [h.energy_eq_square_coefficient]
  apply integral_mono h.toShifted.square_coefficient_integrable
    h.toShifted.denominator_coefficient_integrable
  intro t
  have hp : 0 ≤ Wlog t / denominator (gaussianOffset t) (shiftedSpeed c) * ‖F t‖ ^ 2 :=
    mul_nonneg (div_nonneg (Wlog_pos t).le (denominator_nonneg _ _)) (sq_nonneg _)
  calc
    Wlog t * (gaussianOffset t ^ 2 / denominator (gaussianOffset t) (shiftedSpeed c)) *
        ‖F t‖ ^ 2 =
      (Wlog t / denominator (gaussianOffset t) (shiftedSpeed c) * ‖F t‖ ^ 2) *
        gaussianOffset t ^ 2 := by ring
    _ ≤ (Wlog t / denominator (gaussianOffset t) (shiftedSpeed c) * ‖F t‖ ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left (gaussianOffset_sq_le_one t) hp
    _ = _ := mul_one _

/-- The actual shifted speed lies in a fixed unit disk for all normalized modes. -/
theorem normalized_shiftedSpeed_norm_le_one
    (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) : ‖shiftedSpeed c‖ ≤ 1 := by
  have hlo := (h.normalized_energy_bounds hmass).1
  have hD := h.energy_le_denominator_mass
  have hid := h.energy_eq_potential_sub
  have hpot := integral_Wlog_norm_sq_le (l := l) (r := r) h.regularity.continuous
  rw [hmass, mul_one] at hpot
  have hsq : Complex.normSq (shiftedSpeed c) ≤ 1 := by
    have hnonneg := Complex.normSq_nonneg (shiftedSpeed c)
    nlinarith
  rw [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (shiftedSpeed c)]

/-- A uniform bounded subset of ℂ for spectral subsequence extraction. -/
theorem normalized_speed_norm_lt_two
    (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) : ‖c‖ < 2 := by
  have hz := h.normalized_shiftedSpeed_norm_le_one hmass
  have he : c = shiftedSpeed c + (gaussianCriticalSpeed : ℂ) := by
    simp [shiftedSpeed]
  calc
    ‖c‖ = ‖shiftedSpeed c + (gaussianCriticalSpeed : ℂ)‖ := congrArg norm he
    _ ≤ ‖shiftedSpeed c‖ + ‖(gaussianCriticalSpeed : ℂ)‖ := norm_add_le _ _
    _ = ‖shiftedSpeed c‖ + gaussianCriticalSpeed := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos gaussianCriticalSpeed_pos]
    _ < 2 := by linarith [gaussianCriticalSpeed_lt_one]

end GaussianAnnularMode
end UnforcedLeray.Rayleigh
