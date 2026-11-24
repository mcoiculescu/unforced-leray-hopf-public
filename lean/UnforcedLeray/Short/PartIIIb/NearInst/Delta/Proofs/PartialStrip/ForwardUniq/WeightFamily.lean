import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.Props
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.SigmaDeriv

/-!
# `FUWeightFamily` (item `PartIII-b:C/near/delta/9/1/4`)

Smooth cutoff weights `w(s) = σ(s/δ - 1) σ((t₂ - s)/(t₂ - t₁))` with `σ = Real.smoothTransition`
and `K` from `FUSigmaDeriv`.  Source 3541-3545 (cutoffs on `[δ_j, B]`).

* `w = 0` off `[δ, t₂]` (the first factor vanishes for `s < δ`, the second for `s > t₂`);
* `w = 1` on `[2δ, t₁]` (both factors equal `1` there);
* `w' = σ'(a) σ(b)/δ - σ(a) σ'(b)/(t₂ - t₁)` with `a = s/δ - 1`, `b = (t₂ - s)/(t₂ - t₁)`:
  the second term is `≤ 0`, the first is `≤ K/δ` on `[δ, 2δ]` and vanishes off `[δ, 2δ]`
  (there `a < 0` or `a > 1`, where `σ' = 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem fuWeightFamily : UnforcedLeray.Short.PartIIIb.NearInst.Delta.FUWeightFamily := by
  obtain ⟨K, hK, hσ⟩ := UnforcedLeray.Short.PartIIIb.NearInst.Delta.fuSigmaDeriv
  refine ⟨K, hK, fun δ t₁ t₂ hδ h2t hlt => ?_⟩
  have hpos : 0 < t₂ - t₁ := sub_pos.2 hlt
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hsmd : ∀ x : ℝ, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
    fun x => (hsm.differentiable (by norm_num) x).hasDerivAt
  have hA : ∀ s : ℝ, HasDerivAt (fun x : ℝ => x / δ - 1) (1 / δ) s :=
    fun s => ((hasDerivAt_id' s).div_const δ).sub_const 1
  have hB : ∀ s : ℝ, HasDerivAt (fun x : ℝ => (t₂ - x) / (t₂ - t₁)) ((0 - 1) / (t₂ - t₁)) s :=
    fun s => ((hasDerivAt_const s t₂).sub (hasDerivAt_id' s)).div_const _
  have hwd : ∀ s : ℝ, HasDerivAt
      (fun x : ℝ => Real.smoothTransition (x / δ - 1) *
        Real.smoothTransition ((t₂ - x) / (t₂ - t₁)))
      (deriv Real.smoothTransition (s / δ - 1) * (1 / δ) *
          Real.smoothTransition ((t₂ - s) / (t₂ - t₁)) +
        Real.smoothTransition (s / δ - 1) *
          (deriv Real.smoothTransition ((t₂ - s) / (t₂ - t₁)) * ((0 - 1) / (t₂ - t₁)))) s := by
    intro s
    have h1 : HasDerivAt (Real.smoothTransition ∘ fun x : ℝ => x / δ - 1)
        (deriv Real.smoothTransition (s / δ - 1) * (1 / δ)) s :=
      HasDerivAt.comp s (hsmd (s / δ - 1)) (hA s)
    have h2 : HasDerivAt (Real.smoothTransition ∘ fun x : ℝ => (t₂ - x) / (t₂ - t₁))
        (deriv Real.smoothTransition ((t₂ - s) / (t₂ - t₁)) * ((0 - 1) / (t₂ - t₁))) s :=
      HasDerivAt.comp s (hsmd ((t₂ - s) / (t₂ - t₁))) (hB s)
    exact h1.mul h2
  -- elementary facts on the arguments
  have hA_neg : ∀ s : ℝ, s < δ → s / δ - 1 < 0 := by
    intro s hs
    have : s / δ < 1 := (div_lt_one hδ).2 hs
    linarith
  have hA_big : ∀ s : ℝ, 2 * δ < s → 1 < s / δ - 1 := by
    intro s hs
    have : 2 < s / δ := (lt_div_iff₀ hδ).2 (by linarith)
    linarith
  have hA_ge : ∀ s : ℝ, 2 * δ ≤ s → 1 ≤ s / δ - 1 := by
    intro s hs
    have : 2 ≤ s / δ := (le_div_iff₀ hδ).2 (by linarith)
    linarith
  have hB_ge : ∀ s : ℝ, s ≤ t₁ → 1 ≤ (t₂ - s) / (t₂ - t₁) := by
    intro s hs
    exact (le_div_iff₀ hpos).2 (by linarith)
  have hB_neg : ∀ s : ℝ, t₂ < s → (t₂ - s) / (t₂ - t₁) < 0 := by
    intro s hs
    exact div_neg_of_neg_of_pos (by linarith) hpos
  have hc' : (0 - 1) / (t₂ - t₁) < 0 := div_neg_of_neg_of_pos (by norm_num) hpos
  refine ⟨fun s => Real.smoothTransition (s / δ - 1) *
      Real.smoothTransition ((t₂ - s) / (t₂ - t₁)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    exact (hsm.comp (((contDiff_id).div_const δ).sub contDiff_const)).mul
      (hsm.comp ((contDiff_const.sub contDiff_id).div_const (t₂ - t₁)))
  · -- compact support
    refine HasCompactSupport.intro (isCompact_Icc (a := δ) (b := t₂)) ?_
    intro x hx
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · rw [Real.smoothTransition.zero_of_nonpos (le_of_lt (hA_neg x h)), zero_mul]
    · rw [Real.smoothTransition.zero_of_nonpos (le_of_lt (hB_neg x h)), mul_zero]
  · -- support in `[δ, t₂]`
    have hout : ∀ x : ℝ, x ∉ Icc δ t₂ →
        Real.smoothTransition (x / δ - 1) * Real.smoothTransition ((t₂ - x) / (t₂ - t₁)) = 0 := by
      intro x hx
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h
      · rw [Real.smoothTransition.zero_of_nonpos (le_of_lt (hA_neg x h)), zero_mul]
      · rw [Real.smoothTransition.zero_of_nonpos (le_of_lt (hB_neg x h)), mul_zero]
    refine closure_minimal ?_ isClosed_Icc
    intro x hx
    by_contra h
    exact (Function.mem_support.1 hx) (hout x h)
  · -- values in `[0, 1]`
    intro s
    have h1 := Real.smoothTransition.nonneg (s / δ - 1)
    have h2 := Real.smoothTransition.nonneg ((t₂ - s) / (t₂ - t₁))
    have h3 := Real.smoothTransition.le_one (s / δ - 1)
    have h4 := Real.smoothTransition.le_one ((t₂ - s) / (t₂ - t₁))
    constructor
    · exact mul_nonneg h1 h2
    · nlinarith [mul_nonneg h1 h2]
  · -- `w = 1` on `[2δ, t₁]`
    intro s hs
    dsimp only
    rw [Real.smoothTransition.one_of_one_le (hA_ge s hs.1),
      Real.smoothTransition.one_of_one_le (hB_ge s hs.2), mul_one]
  · -- derivative bound
    intro s
    rw [(hwd s).deriv]
    by_cases hs : s ∈ Icc δ (2 * δ)
    · rw [indicator_of_mem hs]
      simp only [mul_one]
      have hσa0 := Real.smoothTransition.nonneg (s / δ - 1)
      have hσb0 := Real.smoothTransition.nonneg ((t₂ - s) / (t₂ - t₁))
      have hσb1 := Real.smoothTransition.le_one ((t₂ - s) / (t₂ - t₁))
      have hp0 := (hσ (s / δ - 1)).1
      have hpK := (hσ (s / δ - 1)).2.1
      have hu0 := (hσ ((t₂ - s) / (t₂ - t₁))).1
      have hpa : deriv Real.smoothTransition (s / δ - 1) * Real.smoothTransition ((t₂ - s) / (t₂ - t₁))
          ≤ K := by
        nlinarith [mul_le_mul_of_nonneg_left hσb1 hp0]
      have t1 : deriv Real.smoothTransition (s / δ - 1) * (1 / δ) *
          Real.smoothTransition ((t₂ - s) / (t₂ - t₁)) ≤ K / δ := by
        calc deriv Real.smoothTransition (s / δ - 1) * (1 / δ) *
              Real.smoothTransition ((t₂ - s) / (t₂ - t₁))
            = (deriv Real.smoothTransition (s / δ - 1) *
                Real.smoothTransition ((t₂ - s) / (t₂ - t₁))) * (1 / δ) := by ring
          _ ≤ K * (1 / δ) := mul_le_mul_of_nonneg_right hpa (by positivity)
          _ = K / δ := by ring
      have t2 : Real.smoothTransition (s / δ - 1) *
          (deriv Real.smoothTransition ((t₂ - s) / (t₂ - t₁)) * ((0 - 1) / (t₂ - t₁))) ≤ 0 := by
        have hr : 0 ≤ Real.smoothTransition (s / δ - 1) * deriv Real.smoothTransition
            ((t₂ - s) / (t₂ - t₁)) := mul_nonneg hσa0 hu0
        nlinarith [hr]
      linarith
    · rw [indicator_of_notMem hs, mul_zero]
      have hcases : s < δ ∨ 2 * δ < s := by
        simp only [mem_Icc, not_and_or, not_le] at hs
        exact hs
      have hz : deriv Real.smoothTransition (s / δ - 1) = 0 := by
        rcases hcases with h | h
        · exact (hσ (s / δ - 1)).2.2 (Or.inl (hA_neg s h))
        · exact (hσ (s / δ - 1)).2.2 (Or.inr (hA_big s h))
      have hσa0 := Real.smoothTransition.nonneg (s / δ - 1)
      have hu0 := (hσ ((t₂ - s) / (t₂ - t₁))).1
      have hr : 0 ≤ Real.smoothTransition (s / δ - 1) * deriv Real.smoothTransition
          ((t₂ - s) / (t₂ - t₁)) := mul_nonneg hσa0 hu0
      rw [hz]
      simp only [zero_mul, zero_add]
      nlinarith [hr]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
