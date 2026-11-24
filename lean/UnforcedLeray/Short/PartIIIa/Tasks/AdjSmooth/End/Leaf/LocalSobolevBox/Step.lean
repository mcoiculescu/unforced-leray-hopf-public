import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.LocalSobolevBox.Calc

/-!
Cutoff and the double-FTC bound `‖F x‖ₑ ≤ ∫⁻_{box} ‖∂₀∂₁F‖ₑ` for smooth `F` supported in the box
(SP 3060-3061).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.LSB

lemma cutoff (M : ℝ) (hM : 0 ≤ M) :
    ∃ ζ : ℝ × ℝ → ℂ, ContDiff ℝ ∞ ζ ∧ (∀ y, M + 1 ≤ ‖y‖ → ζ y = 0) ∧
      (∀ y, ‖y‖ ≤ M → ζ y = 1) := by
  let a : ContDiffBump (0 : ℝ) := ⟨M + 1 / 2, M + 1, by linarith, by linarith⟩
  refine ⟨fun y => ((a y.1 * a y.2 : ℝ) : ℂ), ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp
      ((a.contDiff.comp contDiff_fst).mul (a.contDiff.comp contDiff_snd))
  · intro y hy
    rw [Prod.norm_def] at hy
    rcases le_max_iff.1 hy with h | h
    · have : a y.1 = 0 := a.zero_of_le_dist (by rw [dist_zero_right]; exact h)
      simp [this]
    · have : a y.2 = 0 := a.zero_of_le_dist (by rw [dist_zero_right]; exact h)
      simp [this]
  · intro y hy
    have h1 : ‖y.1‖ ≤ M := le_trans (by rw [Prod.norm_def]; exact le_max_left _ _) hy
    have h2 : ‖y.2‖ ≤ M := le_trans (by rw [Prod.norm_def]; exact le_max_right _ _) hy
    have e1 : a y.1 = 1 := a.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, dist_zero_right]; show ‖y.1‖ ≤ M + 1 / 2; linarith)
    have e2 : a y.2 = 1 := a.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, dist_zero_right]; show ‖y.2‖ ≤ M + 1 / 2; linarith)
    simp [e1, e2]

lemma closedBall_eq_Icc (R : ℝ) :
    Metric.closedBall (0 : ℝ × ℝ) R = Icc (-R) R ×ˢ Icc (-R) R := by
  ext y
  simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, mem_prod,
    mem_Icc, Real.norm_eq_abs, abs_le]

lemma sup_bound {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (M : ℝ) (hM : 0 ≤ M)
    (hz : ∀ y, M + 1 ≤ ‖y‖ → F y = 0) (x : ℝ × ℝ) (hx : ‖x‖ ≤ M) :
    ‖F x‖ₑ ≤ ∫⁻ y in Metric.closedBall (0 : ℝ × ℝ) (M + 1),
      ‖pdCx 0 (pdCx 1 F) y‖ₑ := by
  have hx1 : |x.1| ≤ M := by
    have := le_trans (by rw [Prod.norm_def]; exact le_max_left _ _ : ‖x.1‖ ≤ ‖x‖) hx
    simpa using this
  have hx2 : |x.2| ≤ M := by
    have := le_trans (by rw [Prod.norm_def]; exact le_max_right _ _ : ‖x.2‖ ≤ ‖x‖) hx
    simpa using this
  set a : ℝ := -(M + 1) with ha
  have hax2 : a ≤ x.2 := by have := neg_abs_le x.2; linarith
  have hax1 : a ≤ x.1 := by have := neg_abs_le x.1; linarith
  have hnorm : ∀ y : ℝ × ℝ, ‖y.1‖ = M + 1 → M + 1 ≤ ‖y‖ := by
    intro y h; rw [Prod.norm_def]; exact h ▸ le_max_left _ _
  have hnorm2 : ∀ y : ℝ × ℝ, ‖y.2‖ = M + 1 → M + 1 ≤ ‖y‖ := by
    intro y h; rw [Prod.norm_def]; exact h ▸ le_max_right _ _
  have hFa : ∀ t, F (a, t) = 0 := fun t => hz _ (hnorm _ (by
    show ‖a‖ = M + 1
    rw [Real.norm_eq_abs, ha, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ M + 1)]))
  have hG : ∀ t, pdCx 1 F (a, t) = 0 := by
    intro t
    have h1 := hasDerivAt_slice1 hF a t
    have h2 : HasDerivAt (fun s => F (a, s)) (0 : ℂ) t := by
      have : (fun s => F (a, s)) = fun _ => (0 : ℂ) := funext hFa
      rw [this]; exact hasDerivAt_const t 0
    exact h1.unique h2
  have hFa2 : F (x.1, a) = 0 := hz _ (hnorm2 _ (by
    show ‖a‖ = M + 1
    rw [Real.norm_eq_abs, ha, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ M + 1)]))
  have hG1 : ContDiff ℝ ∞ (pdCx 1 F) := contDiff_pdCx 1 hF
  have s1 : F x = ∫ t in a..x.2, pdCx 1 F (x.1, t) := by
    have := ftc1 hF a x.1 x.2 hFa2
    simpa using this
  have s1' : ‖F x‖ₑ ≤ ∫⁻ t in Ioc a x.2, ‖pdCx 1 F (x.1, t)‖ₑ := by
    rw [s1, intervalIntegral.integral_of_le hax2]
    exact enorm_integral_le_lintegral_enorm _
  have s2 : ∀ t, ‖pdCx 1 F (x.1, t)‖ₑ ≤
      ∫⁻ s in Ioc a x.1, ‖pdCx 0 (pdCx 1 F) (s, t)‖ₑ := by
    intro t
    have := ftc0 hG1 a x.1 t (hG t)
    rw [this, intervalIntegral.integral_of_le hax1]
    exact enorm_integral_le_lintegral_enorm _
  have hsub1 : Ioc a x.1 ⊆ Icc a (M + 1) := fun s hs => ⟨hs.1.le, by
    have := le_abs_self x.1; linarith [hs.2]⟩
  have hsub2 : Ioc a x.2 ⊆ Icc a (M + 1) := fun s hs => ⟨hs.1.le, by
    have := le_abs_self x.2; linarith [hs.2]⟩
  have hcont : Continuous (pdCx 0 (pdCx 1 F)) := (contDiff_pdCx 0 hG1).continuous
  have hmeas : Measurable (fun y : ℝ × ℝ => ‖pdCx 0 (pdCx 1 F) y‖ₑ) :=
    hcont.measurable.enorm
  calc ‖F x‖ₑ ≤ ∫⁻ t in Ioc a x.2, ‖pdCx 1 F (x.1, t)‖ₑ := s1'
    _ ≤ ∫⁻ t in Ioc a x.2, ∫⁻ s in Ioc a x.1, ‖pdCx 0 (pdCx 1 F) (s, t)‖ₑ :=
        lintegral_mono fun t => s2 t
    _ ≤ ∫⁻ t in Ioc a x.2, ∫⁻ s in Icc a (M + 1), ‖pdCx 0 (pdCx 1 F) (s, t)‖ₑ :=
        lintegral_mono fun t => lintegral_mono_set hsub1
    _ ≤ ∫⁻ t in Icc a (M + 1), ∫⁻ s in Icc a (M + 1), ‖pdCx 0 (pdCx 1 F) (s, t)‖ₑ :=
        lintegral_mono_set hsub2
    _ = ∫⁻ y in Metric.closedBall (0 : ℝ × ℝ) (M + 1), ‖pdCx 0 (pdCx 1 F) y‖ₑ := by
        rw [closedBall_eq_Icc, ← ha, Measure.volume_eq_prod, ← Measure.prod_restrict,
          lintegral_prod_symm _ hmeas.aemeasurable]

end UnforcedLeray.Short.IIIa.LSB
