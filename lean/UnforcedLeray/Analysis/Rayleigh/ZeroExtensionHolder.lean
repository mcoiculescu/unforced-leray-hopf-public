import UnforcedLeray.Analysis.Rayleigh.ZeroExtension
import UnforcedLeray.Analysis.Rayleigh.ZeroExtensionClamp
import UnforcedLeray.Analysis.Rayleigh.IntervalHolder

/-!
# Uniform pointwise bounds for actual zero-extended annular modes

The zero extension equals the original mode composed with the one-Lipschitz
clamp. Its derivative energy therefore gives a global square-root modulus of
continuity, including across the actual annular endpoints.
-/
noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Rayleigh

lemma norm_sub_le_two_sqrt_on_interval {F : ℝ → ℂ} (hF : ContDiff ℝ 1 F)
    {l r a b : ℝ} (ha : a ∈ Icc l r) (hb : b ∈ Icc l r) (hab : a ≤ b)
    (hbound : (∫ x in Ioc l r, ‖deriv F x‖ ^ 2) ≤ 4) :
    ‖F b - F a‖ ≤ 2 * Real.sqrt (b - a) := by
  have hsubset : Ioc a b ⊆ Ioc l r :=
    fun x hx => ⟨lt_of_le_of_lt ha.1 hx.1, hx.2.trans hb.2⟩
  have hi : IntegrableOn (fun x => ‖deriv F x‖ ^ 2) (Ioc l r) :=
    (hF.continuous_deriv_one.norm.pow 2).integrableOn_Ioc
  have hm : (∫ x in Ioc a b, ‖deriv F x‖ ^ 2) ≤ 4 :=
    (setIntegral_mono_set hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (Filter.Eventually.of_forall hsubset)).trans hbound
  have hs : Real.sqrt (∫ x in Ioc a b, ‖deriv F x‖ ^ 2) ≤ 2 := by
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num at hm ⊢; exact hm⟩
  calc
    ‖F b - F a‖ ≤ Real.sqrt (b - a) *
        Real.sqrt (∫ x in Ioc a b, ‖deriv F x‖ ^ 2) :=
      norm_sub_le_sqrt_derivative_mass hF hab
    _ ≤ Real.sqrt (b - a) * 2 :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

namespace ShiftedAnnularMode
variable {q : ℝ → ℝ} {z : ℂ} {F : ℝ → ℂ} {l r : ℝ}
  (h : ShiftedAnnularMode q z F l r)
include h

/-- The actual zero extensions have a uniform 1/2-Hölder modulus. -/
theorem normalized_zeroExtension_holder
    (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) (s t : ℝ) :
    ‖zeroExtension l r F s - zeroExtension l r F t‖ ≤ 2 * Real.sqrt |s - t| := by
  have hD : (∫ x in Ioc l r, ‖deriv F x‖ ^ 2) ≤ 4 := by
    simpa only [integral_norm_sq_zeroExtension] using
      h.normalized_zeroExtension_derivative_bound hmass
  have hF : ContDiff ℝ 1 F := h.regularity.of_le (by norm_num)
  have aux (a b : ℝ) (hab : a ≤ b) :
      ‖zeroExtension l r F b - zeroExtension l r F a‖ ≤ 2 * Real.sqrt |b - a| := by
    rw [zeroExtension_eq_clamp h.ordered h.left_endpoint h.right_endpoint b,
      zeroExtension_eq_clamp h.ordered h.left_endpoint h.right_endpoint a]
    have hc : intervalClamp l r a ≤ intervalClamp l r b :=
      intervalClamp_monotone l r hab
    have hh := norm_sub_le_two_sqrt_on_interval hF
      (intervalClamp_mem h.ordered a) (intervalClamp_mem h.ordered b) hc hD
    have hlen : intervalClamp l r b - intervalClamp l r a ≤ |b - a| := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr hc)] using
        intervalClamp_abs_sub_le l r b a
    exact hh.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlen) (by norm_num))
  rcases le_total s t with hst | hts
  · simpa only [norm_sub_rev, abs_sub_comm] using aux s t hst
  · exact aux t s hts

end ShiftedAnnularMode
end UnforcedLeray.Rayleigh
