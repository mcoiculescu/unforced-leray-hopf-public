import UnforcedLeray.Short.PartIIa.Sub.N02_3

/-!
# Part II-a, task `PartII-a:N02/3` helper: the zero-frequency cutoff `zChi`

Proves `ZeroCutoff` (`Sub/N02_3.lean`), the cutoff property of `zChi(t) = σ(2 - t²)`, where `σ` is
`Real.smoothTransition`. Source of record: `the November 2 reference manuscript`,
lines 1728-1737 ("cut them off at `|η| ~ L₀`").
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

namespace ZeroCutoffAux

lemma zChi_contDiff : ContDiff ℝ ∞ zChi :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

lemma zChi_nonneg (t : ℝ) : 0 ≤ zChi t :=
  Real.smoothTransition.nonneg _

lemma zChi_le_one (t : ℝ) : zChi t ≤ 1 :=
  Real.smoothTransition.le_one _

lemma zChi_eq_one {t : ℝ} (ht : |t| ≤ 1) : zChi t = 1 := by
  have h2 : t ^ 2 ≤ 1 := by
    rw [← sq_abs t]
    nlinarith [abs_nonneg t]
  unfold zChi
  apply Real.smoothTransition.one_of_one_le
  linarith

lemma zChi_eq_zero {t : ℝ} (ht : 2 ≤ |t|) : zChi t = 0 := by
  have h4 : 4 ≤ t ^ 2 := by
    rw [← sq_abs t]
    nlinarith [abs_nonneg t]
  unfold zChi
  apply Real.smoothTransition.zero_of_nonpos
  linarith

lemma zChi_hasCompactSupport : HasCompactSupport zChi := by
  refine HasCompactSupport.intro (K := Icc (-2:ℝ) 2) isCompact_Icc ?_
  intro t ht
  apply zChi_eq_zero
  by_contra h
  have h' : |t| < 2 := not_le.mp h
  exact ht ⟨(abs_lt.1 h').1.le, (abs_lt.1 h').2.le⟩

lemma zChi_deriv_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |deriv zChi t| ≤ M := by
  have hc : Continuous (deriv zChi) :=
    zChi_contDiff.continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support zChi_hasCompactSupport.deriv
  refine ⟨max B 0, le_max_right _ _, fun t => ?_⟩
  have h := hB t
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

end ZeroCutoffAux

/-- **L0 (cutoff).** `zChi` is smooth, `0 ≤ zChi ≤ 1`, equals `1` on `|t| ≤ 1` and `0` for `|t| ≥ 2`,
and has bounded derivative. -/
theorem zeroCutoff : UnforcedLeray.Short.PartIIa.ZeroCutoff :=
  ⟨ZeroCutoffAux.zChi_contDiff,
    fun t => ⟨ZeroCutoffAux.zChi_nonneg t, ZeroCutoffAux.zChi_le_one t⟩,
    fun _ ht => ZeroCutoffAux.zChi_eq_one ht,
    fun _ ht => ZeroCutoffAux.zChi_eq_zero ht,
    ZeroCutoffAux.zChi_deriv_bound⟩

end UnforcedLeray.Short.PartIIa
