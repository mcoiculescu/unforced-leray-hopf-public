import UnforcedLeray.Analysis.Rayleigh.ZeroExtensionHolder

/-! Uniform pointwise boundedness is derived from actual total L² mass and the
proved Hölder modulus, not assumed as input to the annular compactness step. -/
noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Rayleigh

lemma norm_le_four_of_mass_one_holder {G : ℝ → ℂ}
    (hG : MemLp G 2 volume) (hmass : (∫ t, ‖G t‖ ^ 2) = 1)
    (hholder : ∀ s t : ℝ, ‖G s - G t‖ ≤ 2 * Real.sqrt |s - t|) (x : ℝ) :
    ‖G x‖ ≤ 4 := by
  have hi : Integrable (fun t => ‖G t‖ ^ 2) :=
    hG.integrable_norm_pow (by norm_num)
  have hsmall : ∃ y ∈ Ioc x (x + 1), ‖G y‖ ≤ 2 := by
    by_contra hno
    push_neg at hno
    have hlo : (4 : ℝ) ≤ ∫ y in Ioc x (x + 1), ‖G y‖ ^ 2 := by
      have hc : (∫ _y in Ioc x (x + 1), (4 : ℝ)) = 4 := by
        simp [measureReal_def]
      rw [← hc]
      apply setIntegral_mono_on (continuous_const.integrableOn_Ioc) hi.restrict measurableSet_Ioc
      intro y hy
      have hh := hno y hy
      nlinarith [norm_nonneg (G y)]
    have hhi : (∫ y in Ioc x (x + 1), ‖G y‖ ^ 2) ≤ 1 := by
      rw [← hmass]
      exact setIntegral_le_integral hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    linarith
  obtain ⟨y, hy, hnorm⟩ := hsmall
  have hdist : |x - y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hsqrt : Real.sqrt |x - y| ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdist
  have hh := hholder x y
  have hn := norm_add_le (G x - G y) (G y)
  simp only [sub_add_cancel] at hn
  nlinarith

namespace ShiftedAnnularMode
variable {q : ℝ → ℝ} {z : ℂ} {F : ℝ → ℂ} {l r : ℝ}
  (h : ShiftedAnnularMode q z F l r)
include h

theorem normalized_zeroExtension_bound
    (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) (x : ℝ) :
    ‖zeroExtension l r F x‖ ≤ 4 :=
  norm_le_four_of_mass_one_holder (zeroExtension_memLp h.regularity.continuous l r)
    (normalized_zeroExtension_mass hmass) (h.normalized_zeroExtension_holder hmass) x

end ShiftedAnnularMode
end UnforcedLeray.Rayleigh
