import UnforcedLeray.Analysis.Rayleigh.SemicircleEnergy
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Positive real weight for the semicircle identity

The transformed energy weight is nonnegative and integrable on every finite
interval. Its integral is strictly positive for a normalized original mode,
because a vanishing weight forces the transformed mode to vanish almost
 everywhere and hence forces the original mass to be zero.
-/

noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Rayleigh

/-- The real weight appearing after factoring the complex profile square. -/
def semicircleWeight (G : ℝ → ℂ) (t : ℝ) : ℝ :=
  Real.exp (2 * t) * semicircleEnergyDensity G t

theorem semicircleWeight_nonneg (G : ℝ → ℂ) (t : ℝ) :
    0 ≤ semicircleWeight G t :=
  mul_nonneg (Real.exp_pos _).le (semicircleEnergyDensity_nonneg G t)

theorem semicircleWeight_continuous {G : ℝ → ℂ} (hG : ContDiff ℝ 2 G) :
    Continuous (semicircleWeight G) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (semicircleEnergyDensity_continuous hG)

theorem semicircleWeight_integrable {G : ℝ → ℂ} (hG : ContDiff ℝ 2 G)
    (a b : ℝ) : IntegrableOn (semicircleWeight G) (Ioc a b) :=
  (semicircleWeight_continuous hG).integrableOn_Ioc

/-- Vanishing of the real weight forces vanishing of the mode itself. -/
theorem eq_zero_of_semicircleWeight_eq_zero {G : ℝ → ℂ} {t : ℝ}
    (hzero : semicircleWeight G t = 0) : G t = 0 := by
  have hd : semicircleEnergyDensity G t = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (Real.exp_ne_zero _)
  unfold semicircleEnergyDensity at hd
  have hn : ‖G t‖ = 0 := by
    nlinarith [sq_nonneg ‖deriv G t‖, norm_nonneg (G t)]
  exact norm_eq_zero.mp hn

/-- A nonzero original mass prevents the transformed weight from having
zero integral. No regularity of the original factor or mode is needed. -/
theorem semicircleWeight_integral_pos_of_mass_ne_zero {G F H : ℝ → ℂ}
    (hG : ContDiff ℝ 2 G) {a b : ℝ}
    (hfactor : ∀ t, F t = H t * G t)
    (hmass : (∫ t in Ioc a b, ‖F t‖ ^ 2) ≠ 0) :
    0 < ∫ t in Ioc a b, semicircleWeight G t := by
  have hnonneg : 0 ≤ ∫ t in Ioc a b, semicircleWeight G t :=
    integral_nonneg (semicircleWeight_nonneg G)
  by_contra hpos
  have hzero : (∫ t in Ioc a b, semicircleWeight G t) = 0 :=
    le_antisymm (le_of_not_gt hpos) hnonneg
  have hweight : semicircleWeight G =ᵐ[volume.restrict (Ioc a b)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (semicircleWeight_nonneg G))
      (semicircleWeight_integrable hG a b)).mp hzero
  have hFzero : (fun t => ‖F t‖ ^ 2) =ᵐ[volume.restrict (Ioc a b)] fun _ => (0 : ℝ) := by
    filter_upwards [hweight] with t ht
    have hg : G t = 0 := eq_zero_of_semicircleWeight_eq_zero ht
    simp only [hfactor t, hg, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
  apply hmass
  calc
    (∫ t in Ioc a b, ‖F t‖ ^ 2) = ∫ t in Ioc a b, (0 : ℝ) := integral_congr_ae hFzero
    _ = 0 := integral_zero _ _

/-- Strict positivity needed for division in the semicircle moment argument,
derived from the actual mass-one normalization. -/
theorem semicircleWeight_integral_pos {G F H : ℝ → ℂ}
    (hG : ContDiff ℝ 2 G) {a b : ℝ}
    (hfactor : ∀ t, F t = H t * G t)
    (hmass : (∫ t in Ioc a b, ‖F t‖ ^ 2) = 1) :
    0 < ∫ t in Ioc a b, semicircleWeight G t := by
  apply semicircleWeight_integral_pos_of_mass_ne_zero hG hfactor
  rw [hmass]
  norm_num

end UnforcedLeray.Rayleigh
