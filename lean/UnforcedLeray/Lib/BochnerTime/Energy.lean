import UnforcedLeray.Lib.BochnerTime.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Norm bounds and energy identities in time (INF14 target T2)


target T2; decision D15 of `scoping/README.md` §3 (the Hilbert energy identity is built once,
here). Bypass B6 of the scoping note replaces the norm chain rule by the FTC estimate
`‖ũ t‖ ≤ ‖ũ s‖ + ∫ ‖u'‖` and averaging (units B0434, B0435, B0451).

## Main results

* `integral_eq_sub_of_ae_hasDerivAt`: the FTC for a Banach-valued absolutely continuous function
  with an a.e. derivative;
* `HasWeakDerivTime.ae_hasDerivAt_rep`: the representative is a.e. differentiable with
  derivative `u'` (Lebesgue differentiation);
* `HasWeakDerivTime.norm_rep_sub_le`, `abs_norm_rep_sub_norm_rep_le`: increments are bounded by
  `∫_a^b ‖u'‖`;
* `HasWeakDerivTime.sup_le_avg`: `‖ũ t‖ ≤ (b - a)⁻¹ ∫_a^b ‖u‖ + ∫_a^b ‖u'‖`;
* `HasWeakDerivTime.norm_sq_sub`, `norm_sq_sub'`: the Hilbert energy identity
  `‖ũ t‖² - ‖ũ s‖² = 2 ∫_s^t ⟪u', ũ⟫` (also with `u` in place of `ũ`);
* `HasWeakDerivTime.weighted_norm_sq_sub`: the version with a `C¹` scalar weight.

The note's signature of `norm_sq_sub` assumes `u, u' ∈ L²`; only integrability on the bounded
interval is used here, which is weaker.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ContDiff RealInnerProductSpace

namespace UnforcedLeray.BochnerTime

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **FTC for absolutely continuous functions** (Banach valued). If `f` is absolutely continuous
on `uIcc a b`, has derivative `f' x` at a.e. `x ∈ uIcc a b`, and `f'` is interval integrable,
then `∫_a^b f' = f b - f a`. -/
theorem integral_eq_sub_of_ae_hasDerivAt {f f' : ℝ → X} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = f b - f a := by
  have hP := absolutelyContinuousOnInterval_primitive hint (left_mem_uIcc (a := a) (b := b))
  have hG := hf.sub hP
  have hG0 : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt (fun x => f x - ∫ r in a..x, f' r) 0 x := by
    filter_upwards [hd, hint.ae_hasDerivAt_integral] with x h1 h2 hx
    exact ((h1 hx).sub (h2 hx a left_mem_uIcc)).congr_deriv (sub_self _)
  obtain ⟨C, hC⟩ := hG.const_of_ae_hasDerivAt_zero hG0
  have ha : f a - ∫ r in a..a, f' r = C := hC a left_mem_uIcc
  have hb : f b - ∫ r in a..b, f' r = C := hC b right_mem_uIcc
  rw [integral_same, sub_zero] at ha
  rw [← ha] at hb
  rw [← hb]
  abel

/-- The representative is absolutely continuous on `Icc a b`. -/
theorem HasWeakDerivTime.absolutelyContinuousOnInterval_rep {a b : ℝ} {u u' : ℝ → X}
    (h : HasWeakDerivTime a b u u') (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval h.rep a b := by
  have hI : IntervalIntegrable u' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 h.int'
  have hP := absolutelyContinuousOnInterval_primitive hI (left_mem_uIcc (a := a) (b := b))
  refine hP.of_dist_le (K := 1) fun x hx y hy => ?_
  rw [uIcc_of_le hab] at hx hy
  rw [h.rep_eq hab hx, h.rep_eq hab hy, dist_add_left, one_mul]

/-- **Lebesgue differentiation for the representative.** At a.e. `t ∈ Ioo a b` the
representative has derivative `u' t`. -/
theorem HasWeakDerivTime.ae_hasDerivAt_rep {a b : ℝ} {u u' : ℝ → X}
    (h : HasWeakDerivTime a b u u') : ∀ᵐ t, t ∈ Ioo a b → HasDerivAt h.rep (u' t) t := by
  rcases le_or_gt b a with hba | hab
  · exact Eventually.of_forall fun t ht => absurd (ht.1.trans ht.2) (not_lt.2 hba)
  have hI : IntervalIntegrable u' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 h.int'
  filter_upwards [hI.ae_hasDerivAt_integral] with t ht hmem
  have hd : HasDerivAt (fun s => h.rep a + ∫ r in a..s, u' r) (u' t) t :=
    (ht (by rw [uIcc_of_le hab.le]; exact Ioo_subset_Icc_self hmem) a left_mem_uIcc).const_add _
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with s hs
  exact h.rep_eq hab.le (Ioo_subset_Icc_self hs)

/-- **Increment bound.** `‖ũ t - ũ s‖ ≤ ∫_a^b ‖u'‖` for `s, t ∈ Icc a b`. -/
theorem HasWeakDerivTime.norm_rep_sub_le {a b : ℝ} {u u' : ℝ → X}
    (h : HasWeakDerivTime a b u u') {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖h.rep t - h.rep s‖ ≤ ∫ r in a..b, ‖u' r‖ := by
  have hab : a ≤ b := hs.1.trans hs.2
  rw [h.rep_sub_rep hs ht, norm_integral_eq_norm_integral_uIoc, integral_of_le hab]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  have hint' : IntegrableOn u' (Ioc a b) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]; exact h.int'
  have hint : IntegrableOn (fun r => ‖u' r‖) (Ioc a b) := hint'.norm
  refine setIntegral_mono_set hint (Eventually.of_forall fun _ => norm_nonneg _) ?_
  refine LE.le.eventuallyLE ?_
  rw [uIoc]
  exact Ioc_subset_Ioc (le_min hs.1 ht.1) (max_le hs.2 ht.2)

/-- `|‖ũ t‖ - ‖ũ s‖| ≤ ∫_a^b ‖u'‖` for `s, t ∈ Icc a b` (T2). -/
theorem HasWeakDerivTime.abs_norm_rep_sub_norm_rep_le {a b : ℝ} {u u' : ℝ → X}
    (h : HasWeakDerivTime a b u u') {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |‖h.rep t‖ - ‖h.rep s‖| ≤ ∫ r in a..b, ‖u' r‖ :=
  (abs_norm_sub_norm_le _ _).trans (h.norm_rep_sub_le hs ht)

/-- **Averaged sup bound** (T2; bypass B6). For `a < b` and `t ∈ Icc a b`,
`‖ũ t‖ ≤ (b - a)⁻¹ (∫_a^b ‖u‖) + ∫_a^b ‖u'‖`. -/
theorem HasWeakDerivTime.sup_le_avg {a b : ℝ} (hab : a < b) {u u' : ℝ → X}
    (h : HasWeakDerivTime a b u u') {t : ℝ} (ht : t ∈ Icc a b) :
    ‖h.rep t‖ ≤ (b - a)⁻¹ * (∫ r in a..b, ‖u r‖) + ∫ r in a..b, ‖u' r‖ := by
  set B := ∫ r in a..b, ‖u' r‖ with hB
  have hpt : ∀ s ∈ Icc a b, ‖h.rep t‖ - B ≤ ‖h.rep s‖ := by
    intro s hs
    have := h.norm_rep_sub_le hs ht
    have h2 := norm_sub_norm_le (h.rep t) (h.rep s)
    linarith
  have hcont : ContinuousOn (fun s => ‖h.rep s‖) (uIcc a b) := by
    rw [uIcc_of_le hab.le]; exact h.continuousOn_rep.norm
  have hmono := intervalIntegral.integral_mono_on hab.le
    (by simp : IntervalIntegrable (fun _ => ‖h.rep t‖ - B) volume a b)
    hcont.intervalIntegrable hpt
  have heq : ∫ s in a..b, ‖h.rep s‖ = ∫ s in a..b, ‖u s‖ := by
    refine intervalIntegral.integral_congr_ae ?_
    have h1 := (ae_restrict_iff' measurableSet_Ioo).1 h.ae_eq_rep
    have h2 : ∀ᵐ s : ℝ ∂volume, s ≠ b := by simp [ae_iff, measure_singleton]
    filter_upwards [h1, h2] with s hs hsb hmem
    rw [uIoc_of_le hab.le] at hmem
    rw [hs ⟨hmem.1, lt_of_le_of_ne hmem.2 hsb⟩]
  rw [intervalIntegral.integral_const, smul_eq_mul, heq] at hmono
  have hba : 0 < b - a := sub_pos.2 hab
  rw [← sub_le_iff_le_add, inv_mul_eq_div, le_div_iff₀ hba]
  linarith [hmono, mul_comm (b - a) (‖h.rep t‖ - B)]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Interval integrability of `⟪u', ũ⟫` on subintervals of `Icc a b`. -/
theorem HasWeakDerivTime.intervalIntegrable_inner_rep {a b : ℝ} {u u' : ℝ → H}
    (h : HasWeakDerivTime a b u u') {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    IntervalIntegrable (fun r => ⟪u' r, h.rep r⟫) volume s t := by
  have hab : a ≤ b := hs.1.trans hs.2
  have hsub : uIcc s t ⊆ Icc a b := uIcc_subset_Icc hs ht
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn h.continuousOn_rep
  have hI : IntervalIntegrable u' volume s t := by
    have : IntervalIntegrable u' volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 h.int'
    exact this.mono_set (by rw [uIcc_of_le hab]; exact hsub)
  rw [intervalIntegrable_iff] at hI ⊢
  have hcont : ContinuousOn h.rep (uIoc s t) :=
    h.continuousOn_rep.mono (uIoc_subset_uIcc.trans hsub)
  refine (hI.norm.const_mul M).mono' ?_ ?_
  · exact hI.aestronglyMeasurable.inner (hcont.aestronglyMeasurable measurableSet_uIoc)
  · rw [ae_restrict_iff' measurableSet_uIoc]
    refine Eventually.of_forall fun r hr => ?_
    calc ‖⟪u' r, h.rep r⟫‖ ≤ ‖u' r‖ * ‖h.rep r‖ := norm_inner_le_norm _ _
      _ ≤ ‖u' r‖ * M := by
          gcongr; exact hM r (hsub (uIoc_subset_uIcc hr))
      _ = M * ‖u' r‖ := mul_comm _ _

/-- **Hilbert energy identity** (T2). For `s, t ∈ Icc a b`,
`‖ũ t‖² - ‖ũ s‖² = 2 ∫_s^t ⟪u', ũ⟫`. -/
theorem HasWeakDerivTime.norm_sq_sub {a b : ℝ} {u u' : ℝ → H} (h : HasWeakDerivTime a b u u')
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖h.rep t‖ ^ 2 - ‖h.rep s‖ ^ 2 = 2 * ∫ r in s..t, ⟪u' r, h.rep r⟫ := by
  have hab : a ≤ b := hs.1.trans hs.2
  have hsub : uIcc s t ⊆ Icc a b := uIcc_subset_Icc hs ht
  have hsub' : uIcc s t ⊆ uIcc a b := by rw [uIcc_of_le hab]; exact hsub
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn h.continuousOn_rep
  have hAC : AbsolutelyContinuousOnInterval (fun r => ‖h.rep r‖ ^ 2) a b := by
    refine (h.absolutelyContinuousOnInterval_rep hab).of_dist_le (K := 2 * M) fun x hx y hy => ?_
    rw [uIcc_of_le hab] at hx hy
    have hxM := hM x hx
    have hyM := hM y hy
    rw [Real.dist_eq, dist_eq_norm, sq, sq, mul_self_sub_mul_self, abs_mul]
    have h1 : |‖h.rep x‖ + ‖h.rep y‖| ≤ 2 * M := by
      rw [abs_of_nonneg (by positivity)]; linarith
    have h2 : |‖h.rep x‖ - ‖h.rep y‖| ≤ ‖h.rep x - h.rep y‖ := abs_norm_sub_norm_le _ _
    exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith [norm_nonneg (h.rep x)])
  have hd : ∀ᵐ r, r ∈ uIcc s t →
      HasDerivAt (fun r => ‖h.rep r‖ ^ 2) (2 * ⟪u' r, h.rep r⟫) r := by
    have ha : ∀ᵐ r : ℝ ∂volume, r ≠ a := by simp [ae_iff, measure_singleton]
    have hb : ∀ᵐ r : ℝ ∂volume, r ≠ b := by simp [ae_iff, measure_singleton]
    filter_upwards [h.ae_hasDerivAt_rep, ha, hb] with r hr hra hrb hmem
    have hmem' := hsub hmem
    have := (hr ⟨lt_of_le_of_ne hmem'.1 (Ne.symm hra), lt_of_le_of_ne hmem'.2 hrb⟩).norm_sq
    rwa [real_inner_comm] at this
  have hint : IntervalIntegrable (fun r => 2 * ⟪u' r, h.rep r⟫) volume s t :=
    (h.intervalIntegrable_inner_rep hs ht).const_mul 2
  rw [← intervalIntegral.integral_const_mul,
    integral_eq_sub_of_ae_hasDerivAt (hAC.mono hsub') hd hint]

/-- **Hilbert energy identity with `u`** (T2): `‖ũ t‖² - ‖ũ s‖² = 2 ∫_s^t ⟪u', u⟫`. -/
theorem HasWeakDerivTime.norm_sq_sub' {a b : ℝ} {u u' : ℝ → H} (h : HasWeakDerivTime a b u u')
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖h.rep t‖ ^ 2 - ‖h.rep s‖ ^ 2 = 2 * ∫ r in s..t, ⟪u' r, u r⟫ := by
  rw [h.norm_sq_sub hs ht]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  have h1 := (ae_restrict_iff' measurableSet_Ioo).1 h.ae_eq_rep
  have ha : ∀ᵐ r : ℝ ∂volume, r ≠ a := by simp [ae_iff, measure_singleton]
  have hb : ∀ᵐ r : ℝ ∂volume, r ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [h1, ha, hb] with r hr hra hrb hmem
  have hmem' := uIcc_subset_Icc hs ht (uIoc_subset_uIcc hmem)
  rw [hr ⟨lt_of_le_of_ne hmem'.1 (Ne.symm hra), lt_of_le_of_ne hmem'.2 hrb⟩]

/-- **Weighted energy identity** (T2, `C¹` weight). For `w` of class `C¹` and `s, t ∈ Icc a b`,
`w t ‖ũ t‖² - w s ‖ũ s‖² = ∫_s^t (w' ‖ũ‖² + 2 w ⟪u', ũ⟫)`. -/
theorem HasWeakDerivTime.weighted_norm_sq_sub {a b : ℝ} {u u' : ℝ → H}
    (h : HasWeakDerivTime a b u u') {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    w t * ‖h.rep t‖ ^ 2 - w s * ‖h.rep s‖ ^ 2 =
      ∫ r in s..t, (deriv w r * ‖h.rep r‖ ^ 2 + 2 * w r * ⟪u' r, h.rep r⟫) := by
  have hab : a ≤ b := hs.1.trans hs.2
  have hsub : uIcc s t ⊆ Icc a b := uIcc_subset_Icc hs ht
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn h.continuousOn_rep
  have hAC : AbsolutelyContinuousOnInterval (fun r => ‖h.rep r‖ ^ 2) s t := by
    refine ((h.absolutelyContinuousOnInterval_rep hab).mono
      (by rw [uIcc_of_le hab]; exact hsub)).of_dist_le (K := 2 * M) fun x hx y hy => ?_
    have hxM := hM x (hsub hx)
    have hyM := hM y (hsub hy)
    rw [Real.dist_eq, dist_eq_norm, sq, sq, mul_self_sub_mul_self, abs_mul]
    have h1 : |‖h.rep x‖ + ‖h.rep y‖| ≤ 2 * M := by
      rw [abs_of_nonneg (by positivity)]; linarith
    have h2 : |‖h.rep x‖ - ‖h.rep y‖| ≤ ‖h.rep x - h.rep y‖ := abs_norm_sub_norm_le _ _
    exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith [norm_nonneg (h.rep x)])
  have hwAC : AbsolutelyContinuousOnInterval w s t := hw.contDiffOn.absolutelyContinuousOnInterval
  have hprod := hwAC.fun_mul hAC
  have hd : ∀ᵐ r, r ∈ uIcc s t → HasDerivAt (fun r => w r * ‖h.rep r‖ ^ 2)
      (deriv w r * ‖h.rep r‖ ^ 2 + 2 * w r * ⟪u' r, h.rep r⟫) r := by
    have ha : ∀ᵐ r : ℝ ∂volume, r ≠ a := by simp [ae_iff, measure_singleton]
    have hb : ∀ᵐ r : ℝ ∂volume, r ≠ b := by simp [ae_iff, measure_singleton]
    filter_upwards [h.ae_hasDerivAt_rep, ha, hb] with r hr hra hrb hmem
    have hmem' := hsub hmem
    have hn := (hr ⟨lt_of_le_of_ne hmem'.1 (Ne.symm hra), lt_of_le_of_ne hmem'.2 hrb⟩).norm_sq
    have hwd : HasDerivAt w (deriv w r) r :=
      ((hw.differentiable (by simp)) r).hasDerivAt
    exact (hwd.mul hn).congr_deriv (by rw [real_inner_comm]; ring)
  have hint : IntervalIntegrable
      (fun r => deriv w r * ‖h.rep r‖ ^ 2 + 2 * w r * ⟪u' r, h.rep r⟫) volume s t := by
    have hc1 : ContinuousOn (fun r => deriv w r * ‖h.rep r‖ ^ 2) (uIcc s t) :=
      ((hw.continuous_deriv le_rfl).continuousOn).mul
        ((h.continuousOn_rep.mono hsub).norm.pow 2)
    refine hc1.intervalIntegrable.add ?_
    have := (h.intervalIntegrable_inner_rep hs ht).continuousOn_mul
      ((continuous_const.mul hw.continuous).continuousOn (s := uIcc s t) (f := fun r => 2 * w r))
    simpa [mul_assoc] using this
  rw [integral_eq_sub_of_ae_hasDerivAt hprod hd hint]

end Hilbert

end UnforcedLeray.BochnerTime
