import UnforcedLeray.Short.PartIIa.StatementsNear

/-!
# Part II-a, task `PartII-a:N02/4/1` helper: the smooth cutoff `χ` and its scaled version

Helper file for `NzCutoffApprox` (`Tasks/N02LerayComparison/NonzeroMode/Split.lean`), source lines
1729-1736 of `the November 2 reference manuscript`. Here
`χ(t) = σ(2 - t) σ(2 + t)` with `σ` the smooth transition function: `χ = 1` on `[-1, 1]`,
`χ = 0` for `|t| ≥ 2`, `0 ≤ χ ≤ 1`. The cutoff at scale `ε` is `χ(√ε η) = χ(η/L)` with
`L = ε^{-1/2}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- The smooth cutoff `χ(t) = σ(2 - t) σ(2 + t)`. -/
def nzcoChi (t : ℝ) : ℝ := Real.smoothTransition (2 - t) * Real.smoothTransition (2 + t)

lemma nzcoChi_contDiff : ContDiff ℝ ∞ nzcoChi := by
  unfold nzcoChi
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.add contDiff_id))

lemma nzcoChi_differentiable (t : ℝ) : DifferentiableAt ℝ nzcoChi t :=
  (nzcoChi_contDiff.differentiable (by simp)) t

lemma nzcoChi_nonneg (t : ℝ) : 0 ≤ nzcoChi t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma nzcoChi_le_one (t : ℝ) : nzcoChi t ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

lemma nzcoChi_eq_one {t : ℝ} (ht : |t| ≤ 1) : nzcoChi t = 1 := by
  obtain ⟨h1, h2⟩ := abs_le.1 ht
  unfold nzcoChi
  rw [Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ 2 - t by linarith),
    Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ 2 + t by linarith)]
  norm_num

lemma nzcoChi_eq_zero {t : ℝ} (ht : 2 ≤ |t|) : nzcoChi t = 0 := by
  unfold nzcoChi
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht
    rw [Real.smoothTransition.zero_of_nonpos (show 2 - t ≤ 0 by linarith), zero_mul]
  · rw [abs_of_neg h] at ht
    rw [Real.smoothTransition.zero_of_nonpos (show 2 + t ≤ 0 by linarith), mul_zero]

/-- `1 - χ(t) ≤ |t|`, the pointwise bound behind `|1 - χ(η/L)| ≤ |η|/L`. -/
lemma nzcoChi_one_sub_le (t : ℝ) : 1 - nzcoChi t ≤ |t| := by
  by_cases ht : |t| ≤ 1
  · rw [nzcoChi_eq_one ht, sub_self]
    exact abs_nonneg t
  · push_neg at ht
    linarith [nzcoChi_nonneg t]

lemma nzcoChi_hasCompactSupport : HasCompactSupport nzcoChi := by
  refine HasCompactSupport.intro (K := Icc (-2:ℝ) 2) isCompact_Icc ?_
  intro t ht
  apply nzcoChi_eq_zero
  by_contra h
  push_neg at h
  exact ht ⟨(abs_lt.1 h).1.le, (abs_lt.1 h).2.le⟩

/-- Uniform bounds: `|χ'(t)| ≤ B1` and `|t χ'(t)| ≤ B2`. -/
lemma nzco_bounds : ∃ B1 B2 : ℝ, 0 ≤ B1 ∧ 0 ≤ B2 ∧
    ∀ t : ℝ, |deriv nzcoChi t| ≤ B1 ∧ |t * deriv nzcoChi t| ≤ B2 := by
  have hc : Continuous (deriv nzcoChi) :=
    nzcoChi_contDiff.continuous_deriv (by simp)
  obtain ⟨B1, hB1⟩ := hc.bounded_above_of_compact_support nzcoChi_hasCompactSupport.deriv
  have hc2 : Continuous ((fun t : ℝ => t) * deriv nzcoChi) := continuous_id.mul hc
  have hd2 : HasCompactSupport ((fun t : ℝ => t) * deriv nzcoChi) :=
    nzcoChi_hasCompactSupport.deriv.mul_left
  obtain ⟨B2, hB2⟩ := hc2.bounded_above_of_compact_support hd2
  refine ⟨max B1 0, max B2 0, le_max_right _ _, le_max_right _ _, fun t => ⟨?_, ?_⟩⟩
  · have h := hB1 t
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · have h := hB2 t
    simp only [Pi.mul_apply] at h
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)

/-- The cutoff at scale `ε`: `nzcoW ε p = χ(√ε η)`, i.e. `χ(η/L)` with `L = ε^{-1/2}`. -/
def nzcoW (ε : ℝ) (p : Profile) : ℝ := nzcoChi (Real.sqrt ε * p.2.2)

lemma nzcoW_contDiff (ε : ℝ) : ContDiff ℝ ∞ (nzcoW ε) :=
  nzcoChi_contDiff.comp (contDiff_const.mul (contDiff_snd.comp contDiff_snd))

/-- Derivative of the cutoff in `η`: `∂_η χ(√ε η) = χ'(√ε η) √ε`, and `0` in `s` and `q`. -/
lemma nzcoW_fderiv (ε : ℝ) (p v : Profile) :
    fderiv ℝ (nzcoW ε) p v = deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε * v.2.2 := by
  have h1 : HasDerivAt (fun t : ℝ => nzcoChi (Real.sqrt ε * t))
      (deriv nzcoChi (Real.sqrt ε * p.2.2) * (Real.sqrt ε * 1)) p.2.2 :=
    HasDerivAt.comp p.2.2 (nzcoChi_differentiable (Real.sqrt ε * p.2.2)).hasDerivAt
      ((hasDerivAt_id' p.2.2).const_mul (Real.sqrt ε))
  have h2 : HasFDerivAt (fun q : Profile => q.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    hasFDerivAt_snd.comp p hasFDerivAt_snd
  have h3 := HasDerivAt.comp_hasFDerivAt p h1 h2
  have h4 : fderiv ℝ (nzcoW ε) p = (deriv nzcoChi (Real.sqrt ε * p.2.2) * (Real.sqrt ε * 1)) •
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) := h3.fderiv
  rw [h4]
  simp

/-- The cutoff is supported in `|√ε η| < 2`. -/
lemma nzcoW_abs_lt {ε : ℝ} {p : Profile} (h : nzcoW ε p ≠ 0) : |Real.sqrt ε * p.2.2| < 2 := by
  by_contra h2
  push_neg at h2
  exact h (nzcoChi_eq_zero h2)

end UnforcedLeray.Short.PartIIa
