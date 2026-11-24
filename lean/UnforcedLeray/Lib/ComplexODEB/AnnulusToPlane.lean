import UnforcedLeray.Analysis.Rayleigh.WholeLineLimit
import UnforcedLeray.Lib.ComplexODEB.WeakRealSpeed
import UnforcedLeray.Lib.ComplexODEB.WholeLineMode

/-!
# From expanding annular modes to an unstable whole-line mode

Wave 2 block 2H PLAN1b (INF18 O8). `paper/main.tex` lines 1061--1121
(§`sec:st18-1231`, compactness and preservation of a nonzero mode, eqs. `st18-t00038`,
`st18-t00039`; §`sec:st18-1257`, exclusion of every real limiting speed, eq. `st18-t00042`).

*Provenance.* Copy, with namespace `UnforcedLeray.ComplexODEB` and explicit arguments in
place of the dot-notation namespace `UnforcedLeray.Rayleigh.GaussianWholeLineLimit`, of the

unchanged.

Input: a sequence of normalized annular modes `GaussianAnnularMode (c n) (F n) (l n) (r n)`
with `∫_{l n}^{r n} |F n|² = 1`, `l n → -∞`, `r n → ∞`. The compiled
`wholeLineLimit_of_annular_sequence` extracts a nonzero weak `H²` limit with speed in the
closed semicircle and the undivided equation almost everywhere (eq. `st18-t00039`). The
weak real-speed exclusion (`WeakRealSpeed`) gives `Im c_∞ > 0`; the semicircle then gives
`0 < Re c_∞ < 1`; the compiled `gaussianWholeLineMode_of_weak` makes the limit a classical
mode; `WholeLineMode` normalizes it.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh Sturm

section Limit
variable {c : ℕ → ℂ} {F : ℕ → ℝ → ℂ} {l r : ℕ → ℝ}
    {hmode : ∀ n, GaussianAnnularMode (c n) (F n) (l n) (r n)}

/-- Tex lines 1088--1121: the nonzero weak `H²` limit rules out every real limiting
speed, so `Im c_∞ > 0`. -/
theorem wholeLineLimit_speed_im_pos (U : GaussianWholeLineLimit c F l r hmode) :
    0 < U.speed.im := by
  have hn := weak_rayleigh_speed_im_ne_zero
    U.fieldClass U.gradientClass U.residualClass U.fieldClass_ne_zero
    U.fieldClass_weak_first U.fieldClass_weak_second U.equation_class_ae
  exact lt_of_le_of_ne U.speed_im_nonneg hn.symm

/-- Tex line 1121: the semicircle and `Im c_∞ > 0` give `0 < Re c_∞ < 1`. -/
theorem wholeLineLimit_speed_re_strict_bounds (U : GaussianWholeLineLimit c F l r hmode) :
    0 < U.speed.re ∧ U.speed.re < 1 := by
  have hs := U.speed_semicircle
  have hi := sq_pos_of_pos (wholeLineLimit_speed_im_pos U)
  have hr := U.speed_re_bounds
  constructor <;> nlinarith

/-- The continuous compactness limit is a classical unstable whole-line mode. -/
theorem wholeLineLimit_classicalMode (U : GaussianWholeLineLimit c F l r hmode) :
    GaussianWholeLineMode U.speed U.field :=
  gaussianWholeLineMode_of_weak (wholeLineLimit_speed_im_pos U) U.field_continuous
    U.fieldClass_ne_zero U.represents_field U.fieldClass_weak_second U.equation_class_ae

end Limit

/-- Tex lines 1061--1121: normalized annular modes on expanding log-annuli yield a
normalized smooth unstable whole-line mode whose speed lies in the open upper half of the
semicircle disc, with `F` and `F'` decaying at both ends. The annular modes are a
hypothesis here; `Lib/ComplexODEB.lean` supplies them (O7). -/
theorem exists_normalized_wholeLineMode_of_annular_sequence
    (c : ℕ → ℂ) (F : ℕ → ℝ → ℂ) (l r : ℕ → ℝ)
    (hmode : ∀ n, GaussianAnnularMode (c n) (F n) (l n) (r n))
    (hmass : ∀ n, (∫ t in Ioc (l n) (r n), ‖F n t‖ ^ 2) = 1)
    (hl : Tendsto l atTop atBot) (hr : Tendsto r atTop atTop) :
    ∃ (speed : ℂ) (field : ℝ → ℂ),
      GaussianWholeLineMode speed field ∧ (∫ t, ‖field t‖ ^ 2) = 1 ∧
      ContDiff ℝ ∞ field ∧
      (speed.re - 1 / 2) ^ 2 + speed.im ^ 2 ≤ 1 / 4 ∧
      0 < speed.re ∧ speed.re < 1 ∧
      Tendsto field atTop (𝓝 0) ∧ Tendsto field atBot (𝓝 0) ∧
      Tendsto (deriv field) atTop (𝓝 0) ∧ Tendsto (deriv field) atBot (𝓝 0) := by
  obtain ⟨U⟩ := wholeLineLimit_of_annular_sequence c F l r hmode hmass hl hr
  obtain ⟨G, hG, hm⟩ := wholeLineMode_exists_normalized (wholeLineLimit_classicalMode U)
  exact ⟨U.speed, G, hG, hm, wholeLineMode_smooth hG, U.speed_semicircle,
    (wholeLineLimit_speed_re_strict_bounds U).1, (wholeLineLimit_speed_re_strict_bounds U).2,
    (wholeLineMode_decay hG).1, (wholeLineMode_decay hG).2,
    (wholeLineMode_derivative_decay hG).1, (wholeLineMode_derivative_decay hG).2⟩

end UnforcedLeray.ComplexODEB
