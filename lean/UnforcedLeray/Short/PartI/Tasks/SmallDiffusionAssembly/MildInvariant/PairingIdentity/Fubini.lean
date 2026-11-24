import UnforcedLeray.Short.PartI.Sub.PartI_C05_4

/-!
# Helper for `PartI:C05/4/3`: Fubini on the triangle `s ≤ r ≤ τ ≤ t`.

Swaps `∫_s^t (∫_r^t G r τ dτ) dr` with `∫_s^t (∫_s^τ G r τ dr) dτ` for a bounded
measurable `G`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace UnforcedLeray.Short.PartI.PairingFubini

theorem triangle_swap (G : ℝ → ℝ → ℂ) {s t : ℝ} (hst : s ≤ t)
    (hm : StronglyMeasurable (fun p : ℝ × ℝ => G p.1 p.2)) (C : ℝ)
    (hC : ∀ x ∈ Icc s t, ∀ y ∈ Icc s t, ‖G x y‖ ≤ C) :
    ∫ r in s..t, ∫ τ in r..t, G r τ = ∫ τ in s..t, ∫ r in s..τ, G r τ := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC s ⟨le_rfl, hst⟩ s ⟨le_rfl, hst⟩)
  set F : ℝ → ℝ → ℂ := fun r τ => Set.indicator (Ioi r) (G r) τ with hF
  have step1 : ∀ r ∈ uIcc s t, ∫ τ in r..t, G r τ = ∫ τ in Ioc s t, F r τ := by
    intro r hr
    rw [uIcc_of_le hst] at hr
    have hset : Ioc s t ∩ Ioi r = Ioc r t := by
      ext x
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by linarith [hr.1], h2⟩, h1⟩
    rw [intervalIntegral.integral_of_le hr.2]
    simp only [hF]
    rw [setIntegral_indicator measurableSet_Ioi, hset]
  have step2 : ∫ r in s..t, ∫ τ in r..t, G r τ = ∫ r in s..t, ∫ τ in Ioc s t, F r τ :=
    intervalIntegral.integral_congr (fun r hr => step1 r hr)
  have hmeasF : StronglyMeasurable (Function.uncurry F) := by
    have heq : Function.uncurry F = fun p : ℝ × ℝ =>
        Set.indicator {q : ℝ × ℝ | q.1 < q.2} (fun q => G q.1 q.2) p := by
      funext p
      simp only [Function.uncurry, hF, Set.indicator_apply, Set.mem_Ioi, Set.mem_setOf_eq]
    rw [heq]
    exact hm.indicator (measurableSet_lt measurable_fst measurable_snd)
  have : IsFiniteMeasure (volume.restrict (Ioc s t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.uIoc s t)).prod (volume.restrict (Ioc s t))) := by
    rw [uIoc_of_le hst]
    refine Integrable.of_bound hmeasF.aestronglyMeasurable C ?_
    rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)]
    refine Eventually.of_forall (fun p hp => ?_)
    obtain ⟨h1, h2⟩ := hp
    simp only [Function.uncurry, hF, Set.indicator_apply, Set.mem_Ioi]
    split_ifs
    · exact hC p.1 (Ioc_subset_Icc_self h1) p.2 (Ioc_subset_Icc_self h2)
    · simp [hC0]
  have step3 := intervalIntegral_integral_swap (f := F) hint
  have step4 : ∀ τ ∈ Ioc s t, ∫ r in s..t, F r τ = ∫ r in s..τ, G r τ := by
    intro τ hτ
    have hfun : (fun r => F r τ) = Set.indicator (Iio τ) (fun r => G r τ) := by
      funext r
      simp only [hF, Set.indicator_apply, Set.mem_Ioi, Set.mem_Iio]
    have hset : Ioc s t ∩ Iio τ = Ioo s τ := by
      ext x
      simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, le_trans h3.le hτ.2⟩, h3⟩
    rw [intervalIntegral.integral_of_le hst, hfun, setIntegral_indicator measurableSet_Iio, hset,
      intervalIntegral.integral_of_le hτ.1.le, integral_Ioc_eq_integral_Ioo]
  rw [step2, step3]
  rw [intervalIntegral.integral_of_le hst]
  refine setIntegral_congr_fun measurableSet_Ioc (fun τ hτ => ?_)
  exact step4 τ hτ

end UnforcedLeray.Short.PartI.PairingFubini
