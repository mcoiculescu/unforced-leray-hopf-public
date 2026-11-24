import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.FlatGraphOrg
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
Leaf `PartII-b:T13/1/1` (SP 1928-1930): the window cutoff `winCut a s = winCut1 (s/a)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

/-- Helper: the base cutoff vanishes for `s ≤ 1/2` and for `s ≥ 4`. -/
theorem wcp_winCut1_zero (s : ℝ) (h : s ≤ 1 / 2 ∨ 4 ≤ s) : winCut1 s = 0 := by
  rcases h with h | h
  · have h1 : 2 * s - 1 ≤ 0 := by linarith
    unfold winCut1
    rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]
  · have h1 : (4 - s) / 2 ≤ 0 := by linarith
    unfold winCut1
    rw [Real.smoothTransition.zero_of_nonpos h1, mul_zero]

/-- Helper: the base cutoff is `1` on `[1, 2]`. -/
theorem wcp_winCut1_one (t : ℝ) (h1 : 1 ≤ t) (h2 : t ≤ 2) : winCut1 t = 1 := by
  unfold winCut1
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * t - 1),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ (4 - t) / 2), mul_one]

/-- Helper: the base cutoff is smooth. -/
theorem wcp_winCut1_contDiff : ContDiff ℝ ∞ winCut1 := by
  unfold winCut1
  apply ContDiff.mul
  · exact Real.smoothTransition.contDiff.comp (by fun_prop)
  · exact Real.smoothTransition.contDiff.comp (by fun_prop)

/-- Helper: the base cutoff has compact support. -/
theorem wcp_winCut1_compact : HasCompactSupport winCut1 := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 4))
  intro x hx
  apply wcp_winCut1_zero
  by_contra hcon
  push_neg at hcon
  exact hx ⟨by linarith [hcon.1], by linarith [hcon.2]⟩

/-- Helper: a uniform bound on the derivative of the base cutoff. -/
theorem wcp_deriv_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |deriv winCut1 t| ≤ M := by
  have hc : Continuous (deriv winCut1) := wcp_winCut1_contDiff.continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv winCut1) := wcp_winCut1_compact.deriv
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  have := hC t
  rw [Real.norm_eq_abs] at this
  exact le_max_of_le_left this

/-- Helper: the base cutoff is in `[0, 1]`. -/
theorem wcp_winCut1_bounds (t : ℝ) : 0 ≤ winCut1 t ∧ winCut1 t ≤ 1 := by
  unfold winCut1
  refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _), ?_⟩
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

/-- **Leaf `PartII-b:T13/1/1`** (SP 1928-1930): the properties of the cutoff `χ_a`. -/
theorem winCutProps : WinCutProps := by
  obtain ⟨M, hM0, hM⟩ := wcp_deriv_bound
  refine ⟨M, hM0, fun a ha => ?_⟩
  have hfun : winCut a = fun s => winCut1 (s / a) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hfun]
    exact wcp_winCut1_contDiff.comp ((contDiff_id).div_const a)
  · intro s hs
    rw [show winCut a s = winCut1 (s / a) from rfl]
    apply wcp_winCut1_one
    · rw [le_div_iff₀ ha]; linarith [hs.1]
    · rw [div_le_iff₀ ha]; linarith [hs.2]
  · apply closure_minimal _ isClosed_Icc
    intro s hs
    by_contra hcon
    apply hs
    rw [show winCut a s = winCut1 (s / a) from rfl]
    apply wcp_winCut1_zero
    rw [mem_Icc, not_and_or, not_le, not_le] at hcon
    rcases hcon with h | h
    · left
      rw [div_le_iff₀ ha]
      linarith
    · right
      rw [le_div_iff₀ ha]
      linarith
  · intro s
    rw [show winCut a s = winCut1 (s / a) from rfl]
    exact wcp_winCut1_bounds _
  · intro s
    have hg : HasDerivAt winCut1 (deriv winCut1 (s / a)) (s / a) :=
      ((wcp_winCut1_contDiff.differentiable (by simp)) _).hasDerivAt
    have hl : HasDerivAt (fun x : ℝ => x / a) (1 / a) s :=
      (hasDerivAt_id' s).div_const a
    have hd : HasDerivAt (winCut1 ∘ fun x : ℝ => x / a) (deriv winCut1 (s / a) * (1 / a)) s :=
      HasDerivAt.comp s hg hl
    rw [show deriv (winCut a) s = deriv (winCut1 ∘ fun x : ℝ => x / a) s from rfl, hd.deriv,
      abs_mul, abs_of_pos (one_div_pos.2 ha), mul_one_div]
    have hb := hM (s / a)
    gcongr

end UnforcedLeray.Short.IIb
