import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4.VtvFubiniInner.Jet
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FubiniInner

/-- Real fundamental theorem of calculus on `[r, ∞)` for a compactly supported-in-`s` function. -/
theorem real_ftc {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) {s1 s2 : ℝ} {R : ℝ}
    (hz : ∀ p : ℝ × (ℝ × ℝ), (p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|) → H p = 0)
    {r : ℝ} (hr : 0 < r) (x : ℝ × ℝ) :
    ∫ s in Ioi (0 : ℝ), (if r ≤ s then Ds H (s, x) else 0) = - H (r, x) := by
  have hU : IsOpen {p : ℝ × (ℝ × ℝ) | p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|} := by
    refine (isOpen_lt continuous_fst continuous_const).union ?_
    exact (isOpen_lt continuous_const continuous_fst).union
      (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd)))
  have hDz := zero_Ds hU hz
  have hcont : Continuous (fun s : ℝ => Ds H (s, x)) :=
    (smooth_Ds hH).continuous.comp (continuous_id.prodMk continuous_const)
  have e : (fun s : ℝ => if r ≤ s then Ds H (s, x) else 0) =
      (Ici r).indicator (fun s => Ds H (s, x)) := by
    funext s; simp [Set.indicator_apply]
  rw [e, setIntegral_indicator measurableSet_Ici]
  have hi : Ioi (0 : ℝ) ∩ Ici r = Ici r := by
    ext s; simp only [mem_inter_iff, mem_Ioi, mem_Ici]
    exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le hr h, h⟩⟩
  rw [hi, integral_Ici_eq_integral_Ioi]
  have hsupp : HasCompactSupport (fun s : ℝ => Ds H (s, x)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := s1) (b := s2)) ?_
    intro s hs
    apply hDz
    simp only [mem_Icc, not_and_or, not_le] at hs
    rcases hs with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hint : IntegrableOn (fun s : ℝ => Ds H (s, x)) (Ioi r) :=
    (hcont.integrable_of_hasCompactSupport hsupp).integrableOn
  have hlim : Tendsto (fun s : ℝ => H (s, x)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop s2] with s hs
    exact (hz (s, x) (Or.inr (Or.inl hs))).symm
  have hd : ∀ s ∈ Ioi r, HasDerivAt (fun s' => H (s', x)) (Ds H (s, x)) s :=
    fun s _ => hasDerivAt_s hH s x
  have hcw : ContinuousWithinAt (fun s' => H (s', x)) (Ici r) r :=
    ((hH.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt).continuousWithinAt
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcw hd hint hlim
  rw [this]
  ring

theorem exch {c : ℝ} {B : ℝ × ℝ → ℂ} (hB : IntegrableOn B (B0579.cell c))
    {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) {s1 s2 R : ℝ}
    (hz : ∀ p : ℝ × (ℝ × ℝ), (p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|) → H p = 0)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun s : ℝ => if r ≤ s then ∫ x in B0579.cell c, B x * (Ds H (s, x) : ℂ) else 0)
        (volume.restrict (Ioi (0 : ℝ))) ∧
      ∫ s in Ioi (0 : ℝ), (if r ≤ s then ∫ x in B0579.cell c, B x * (Ds H (s, x) : ℂ) else 0) =
        - ∫ x in B0579.cell c, B x * (H (r, x) : ℂ) := by
  have hU : IsOpen {p : ℝ × (ℝ × ℝ) | p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|} := by
    refine (isOpen_lt continuous_fst continuous_const).union ?_
    exact (isOpen_lt continuous_const continuous_fst).union
      (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd)))
  have hDz := zero_Ds hU hz
  have hDc : Continuous (Ds H) := (smooth_Ds hH).continuous
  -- bound
  set K : Set (ℝ × (ℝ × ℝ)) :=
    Icc s1 s2 ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-|R|) |R|) with hK
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hDc.continuousOn
  set M : ℝ := max C 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hbound : ∀ p : ℝ × (ℝ × ℝ), p.2 ∈ B0579.cell c →
      ‖Ds H p‖ ≤ (Icc s1 s2).indicator (fun _ => M) p.1 := by
    intro p hp
    by_cases h1 : p.1 ∈ Icc s1 s2
    · rw [Set.indicator_of_mem h1]
      by_cases h2 : |p.2.2| ≤ |R|
      · have hpK : p ∈ K := by
          refine ⟨h1, ?_, ?_⟩
          · have := hp.1
            exact ⟨this.1, this.2.le⟩
          · exact abs_le.1 h2
        exact (hC p hpK).trans (le_max_left _ _)
      · push_neg at h2
        have : Ds H p = 0 := hDz p (Or.inr (Or.inr (lt_of_le_of_lt (le_abs_self R) h2)))
        simp [this, hM0]
    · rw [Set.indicator_of_notMem h1]
      have : Ds H p = 0 := by
        apply hDz
        simp only [mem_Icc, not_and_or, not_le] at h1
        rcases h1 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      simp [this]
  -- product integrand
  let F : ℝ × (ℝ × ℝ) → ℂ := fun p => if r ≤ p.1 then B p.2 * (Ds H p : ℂ) else 0
  have hmeas : MeasurableSet {p : ℝ × (ℝ × ℝ) | r ≤ p.1} := measurableSet_le measurable_const measurable_fst
  have hFe : F = {p : ℝ × (ℝ × ℝ) | r ≤ p.1}.indicator (fun p => B p.2 * (Ds H p : ℂ)) := by
    funext p; simp [F, Set.indicator_apply]
  have hμ : (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c)) =
      (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
    rfl
  have hFint : Integrable F ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c))) := by
    have hg : Integrable (fun p : ℝ × (ℝ × ℝ) =>
        (Icc s1 s2).indicator (fun _ => M) p.1 * ‖B p.2‖)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c))) := by
      refine Integrable.mul_prod (f := fun s : ℝ => (Icc s1 s2).indicator (fun _ => M) s)
        (g := fun x : ℝ × ℝ => ‖B x‖) ?_ hB.norm
      exact (integrable_indicator_iff measurableSet_Icc).2
        (integrableOn_const (by
          rw [Measure.restrict_apply measurableSet_Icc]
          exact ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top).ne))
    refine hg.mono' ?_ ?_
    · rw [hFe]
      refine AEStronglyMeasurable.indicator ?_ hmeas
      have h1 : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => B p.2)
          ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c))) :=
        hB.aestronglyMeasurable.comp_snd
      exact h1.mul (Complex.continuous_ofReal.comp hDc).aestronglyMeasurable
    · rw [hμ]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod (B0579.measurableSet_cell c))] with p hp
      simp only [F]
      split_ifs with h
      · rw [norm_mul, Complex.norm_real, mul_comm]
        exact mul_le_mul_of_nonneg_right (hbound p hp.2) (norm_nonneg _)
      · simp only [norm_zero]
        exact mul_nonneg (Set.indicator_nonneg (fun _ _ => hM0) _) (norm_nonneg _)
  have hslice : (fun s : ℝ => ∫ x in B0579.cell c, F (s, x)) =
      fun s : ℝ => if r ≤ s then ∫ x in B0579.cell c, B x * (Ds H (s, x) : ℂ) else 0 := by
    funext s; simp only [F]; split_ifs <;> simp
  have hI1 := hFint.integral_prod_left
  rw [hslice] at hI1
  refine ⟨hI1, ?_⟩
  rw [← hslice]
  have hswap := integral_integral_swap (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (B0579.cell c)) (f := fun s x => F (s, x)) hFint
  rw [hswap]
  have hin : ∀ x : ℝ × ℝ, ∫ s in Ioi (0 : ℝ), F (s, x) = - (B x * (H (r, x) : ℂ)) := by
    intro x
    have e : (fun s : ℝ => F (s, x)) = fun s : ℝ =>
        B x * (((if r ≤ s then Ds H (s, x) else 0 : ℝ)) : ℂ) := by
      funext s; simp only [F]; split_ifs <;> simp
    simp only [e]
    rw [integral_const_mul, integral_complex_ofReal, real_ftc hH hz hr x]
    push_cast
    ring
  simp_rw [hin]
  rw [integral_neg]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FubiniInner
