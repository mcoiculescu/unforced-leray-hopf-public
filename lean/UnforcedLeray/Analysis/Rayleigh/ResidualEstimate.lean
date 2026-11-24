import UnforcedLeray.Analysis.Rayleigh.EnergyEstimates
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Uniform second-derivative residual estimate for actual annular modes

The actual differential equation expresses the residual by the critical
coefficient. The exact imaginary-moment cancellation and Wlog ≤ 8 then bound
its L² norm independently of the distance of the speed to the real axis.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace UnforcedLeray.Rayleigh
open GaussianPotential Sturm
namespace ShiftedAnnularMode
variable {q : ℝ → ℝ} {z : ℂ} {F : ℝ → ℂ} {l r : ℝ}
  (h : ShiftedAnnularMode q z F l r)
include h

/-- The differential residual is genuinely square integrable on the annulus. -/
theorem freeResidual_memLp :
    MemLp (fun t => deriv (deriv F) t - 4 * F t) 2 (volume.restrict (Ioc l r)) := by
  have hc := (continuous_second_of_two h.regularity).sub (h.regularity.continuous.const_mul 4)
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    (freeResidual_norm_sq_integrable h.regularity l r)

/-- Pointwise use of the concrete ODE and the exact potential bound. -/
theorem freeResidual_sq_le {t : ℝ} (ht : t ∈ Ioc l r) :
    ‖deriv (deriv F) t - 4 * F t‖ ^ 2 ≤
      8 * (Wlog t * (q t ^ 2 / denominator (q t) z) * ‖F t‖ ^ 2) := by
  rw [h.equation t ht, neg_mul, norm_neg, forcing_norm_sq]
  have hc : 0 ≤ Wlog t * (q t ^ 2 / denominator (q t) z) * ‖F t‖ ^ 2 :=
    mul_nonneg (mul_nonneg (Wlog_pos t).le
      (div_nonneg (sq_nonneg _) (denominator_nonneg _ _))) (sq_nonneg _)
  calc
    Wlog t ^ 2 * (q t ^ 2 / denominator (q t) z) * ‖F t‖ ^ 2 =
        Wlog t * (Wlog t * (q t ^ 2 / denominator (q t) z) * ‖F t‖ ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Wlog_le_eight t) hc

/-- The actual integral residual bound has no factor 1/Im z. -/
theorem integral_freeResidual_sq_le_energy :
    (∫ t in Ioc l r, ‖deriv (deriv F) t - 4 * F t‖ ^ 2) ≤
      8 * intervalEnergy F l r := by
  rw [h.energy_eq_square_coefficient, ← integral_const_mul]
  exact setIntegral_mono_on (freeResidual_norm_sq_integrable h.regularity l r)
    (h.square_coefficient_integrable.const_mul 8) measurableSet_Ioc
    (fun t ht => h.freeResidual_sq_le ht)

/-- For mass-one modes the actual squared residual is at most 64. -/
theorem normalized_integral_freeResidual_sq_le
    (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) :
    (∫ t in Ioc l r, ‖deriv (deriv F) t - 4 * F t‖ ^ 2) ≤ 64 := by
  have he := (h.normalized_energy_bounds hmass).2
  have hr := h.integral_freeResidual_sq_le_energy
  linarith

/-- The actual restricted L² seminorm is bounded by eight, with membership
proved separately so taking its real value cannot hide infinity. -/
theorem normalized_freeResidual_l2_le
    (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) :
    (eLpNorm (fun t => deriv (deriv F) t - 4 * F t) 2
      (volume.restrict (Ioc l r))).toReal ≤ 8 := by
  have hm := h.freeResidual_memLp
  have hs : (eLpNorm (fun t => deriv (deriv F) t - 4 * F t) 2
      (volume.restrict (Ioc l r))).toReal ^ 2 =
      ∫ t in Ioc l r, ‖deriv (deriv F) t - 4 * F t‖ ^ 2 := by
    rw [hm.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    have h0 : 0 ≤ ∫ t in Ioc l r,
        ‖deriv (deriv F) t - 4 * F t‖ ^ (2 : ENNReal).toReal :=
      integral_nonneg fun _ => by positivity
    rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h0]
    simp
  have hb := h.normalized_integral_freeResidual_sq_le hmass
  nlinarith

end ShiftedAnnularMode
end UnforcedLeray.Rayleigh
