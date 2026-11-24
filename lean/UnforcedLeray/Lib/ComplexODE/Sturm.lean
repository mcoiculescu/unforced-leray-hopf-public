import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Monotone

/-!
# Sturm comparison on a bounded interval (generic real lemmas)

Wave 1 block 1H part 3 (INF18 target O1, scoping note

These lemmas replace the min--max and counting arguments behind `paper/main.tex`
lines 941--948 (eq. st18-t00030, units B0028--B0029) and the variational threshold
of lines 1001--1011 (eq. st18-t00032, unit B0034) in the annular neutral problem: they are
the classical Sturm comparison theorem by the Wronskian, and the existence of a first zero.

* `exists_pos_Ioo_of_hasDerivAt_pos`: a zero with positive slope is followed by positivity;
* `exists_first_zero`: a function positive just after `p` and nonpositive at `q` has a first
  zero in `(p, q]`;
* `sturm_comparison_false`: if `u'' = q_u u`, `h'' = q_h h`, `q_h < q_u` on `(p, r)`,
  `u(p) = u(r) = 0` and `u, h > 0` on `(p, r)`, there is a contradiction.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace UnforcedLeray.ComplexODE

/-- A function continuous at `p` and positive on `(p, r)` is nonnegative at `p`. -/
theorem nonneg_left_of_pos_Ioo {u : ℝ → ℝ} {p r : ℝ} (hpr : p < r) (hu : ContinuousAt u p)
    (hpos : ∀ t ∈ Ioo p r, 0 < u t) : 0 ≤ u p :=
  ge_of_tendsto (hu.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.mem_of_superset (Ioo_mem_nhdsGT hpr) fun t ht => (hpos t ht).le)

/-- A function continuous at `r` and positive on `(p, r)` is nonnegative at `r`. -/
theorem nonneg_right_of_pos_Ioo {u : ℝ → ℝ} {p r : ℝ} (hpr : p < r) (hu : ContinuousAt u r)
    (hpos : ∀ t ∈ Ioo p r, 0 < u t) : 0 ≤ u r :=
  ge_of_tendsto (hu.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.mem_of_superset (Ioo_mem_nhdsLT hpr) fun t ht => (hpos t ht).le)

/-- At a zero followed by positivity, the slope is nonnegative. -/
theorem deriv_nonneg_of_zero_of_pos_right {u : ℝ → ℝ} {d p r : ℝ} (hpr : p < r)
    (hd : HasDerivAt u d p) (hp : u p = 0) (hpos : ∀ t ∈ Ioo p r, 0 < u t) : 0 ≤ d := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsGT_le_nhdsNE p)
  apply ge_of_tendsto hs
  filter_upwards [Ioo_mem_nhdsGT hpr] with t ht
  rw [slope_def_field, hp, sub_zero]
  exact div_nonneg (hpos t ht).le (sub_pos.mpr ht.1).le

/-- At a zero preceded by positivity, the slope is nonpositive. -/
theorem deriv_nonpos_of_zero_of_pos_left {u : ℝ → ℝ} {d p r : ℝ} (hpr : p < r)
    (hd : HasDerivAt u d r) (hr : u r = 0) (hpos : ∀ t ∈ Ioo p r, 0 < u t) : d ≤ 0 := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsLT_le_nhdsNE r)
  apply le_of_tendsto hs
  filter_upwards [Ioo_mem_nhdsLT hpr] with t ht
  rw [slope_def_field, hr, sub_zero]
  exact div_nonpos_of_nonneg_of_nonpos (hpos t ht).le (sub_neg.mpr ht.2).le

/-- A zero with positive slope is followed by an interval of positivity. -/
theorem exists_pos_Ioo_of_hasDerivAt_pos {u : ℝ → ℝ} {d p : ℝ} (hd : HasDerivAt u d p)
    (hp : u p = 0) (hd0 : 0 < d) : ∃ δ > 0, ∀ t ∈ Ioo p (p + δ), 0 < u t := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsGT_le_nhdsNE p)
  have hev : ∀ᶠ t in 𝓝[>] p, 0 < slope u p t := hs.eventually (Ioi_mem_nhds hd0)
  have hev' : ∀ᶠ t in 𝓝[>] p, 0 < u t := by
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htp
    rw [slope_def_field, hp, sub_zero] at ht
    exact (div_pos_iff_of_pos_right (sub_pos.mpr htp)).mp ht
  obtain ⟨q, hq, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev'
  refine ⟨q - p, sub_pos.mpr hq, fun t ht => hsub ?_⟩
  simpa using ht

/-- A continuous function that is positive just after `p` and nonpositive at `q > p` has a
first zero `r ∈ (p, q]`, with positivity on `(p, r)`. -/
theorem exists_first_zero {u : ℝ → ℝ} {p q : ℝ} (hu : Continuous u) (hpq : p < q)
    (hstart : ∃ δ > 0, ∀ t ∈ Ioo p (p + δ), 0 < u t) (hq : u q ≤ 0) :
    ∃ r ∈ Ioc p q, u r = 0 ∧ ∀ t ∈ Ioo p r, 0 < u t := by
  obtain ⟨δ, hδ, hδpos⟩ := hstart
  set p' : ℝ := p + min δ (q - p) / 2 with hp'
  have hm : 0 < min δ (q - p) := lt_min hδ (sub_pos.mpr hpq)
  have hpp' : p < p' := by rw [hp']; linarith
  have hp'δ : p' < p + δ := by
    rw [hp']; linarith [min_le_left δ (q - p)]
  have hp'q : p' < q := by
    rw [hp']; linarith [min_le_right δ (q - p)]
  set Z : Set ℝ := Icc p' q ∩ {t | u t ≤ 0} with hZ
  have hZc : IsClosed Z := isClosed_Icc.inter (isClosed_le hu continuous_const)
  have hZne : Z.Nonempty := ⟨q, ⟨hp'q.le, le_rfl⟩, hq⟩
  have hZb : BddBelow Z := ⟨p', fun t ht => ht.1.1⟩
  set r := sInf Z with hr
  have hrZ : r ∈ Z := hZc.csInf_mem hZne hZb
  have hpr : p < r := hpp'.trans_le hrZ.1.1
  have hpos : ∀ t ∈ Ioo p r, 0 < u t := by
    intro t ht
    by_cases htp : t < p + δ
    · exact hδpos t ⟨ht.1, htp⟩
    · by_contra hneg
      have htZ : t ∈ Z := ⟨⟨by linarith, (ht.2.trans_le hrZ.1.2).le⟩, not_lt.mp hneg⟩
      exact absurd (csInf_le hZb htZ) (not_le.mpr ht.2)
  have hr0 : u r = 0 :=
    le_antisymm hrZ.2 (nonneg_right_of_pos_Ioo hpr hu.continuousAt hpos)
  exact ⟨r, ⟨hpr, hrZ.1.2⟩, hr0, hpos⟩

/-- **Sturm comparison.** Let `u'' = q_u u` and `h'' = q_h h` with `q_h < q_u` on `(p, r)`.
If `u` vanishes at `p` and `r` and both `u` and `h` are positive on `(p, r)`, this is
contradictory: the Wronskian `u' h - u h'` is strictly increasing on `[p, r]`, nonnegative at
`p` and nonpositive at `r`. -/
theorem sturm_comparison_false {u u' h h' qu qh : ℝ → ℝ} {p r : ℝ} (hpr : p < r)
    (hu : ∀ t, HasDerivAt u (u' t) t) (hu' : ∀ t, HasDerivAt u' (qu t * u t) t)
    (hh : ∀ t, HasDerivAt h (h' t) t) (hh' : ∀ t, HasDerivAt h' (qh t * h t) t)
    (hqu : Continuous qu) (hqh : Continuous qh)
    (hlt : ∀ t ∈ Ioo p r, qh t < qu t)
    (hup : u p = 0) (hur : u r = 0) (hupos : ∀ t ∈ Ioo p r, 0 < u t)
    (hhpos : ∀ t ∈ Ioo p r, 0 < h t) : False := by
  have huc : Continuous u := continuous_iff_continuousAt.2 fun t => (hu t).continuousAt
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hh t).continuousAt
  set w : ℝ → ℝ := fun t => u' t * h t - u t * h' t with hw
  have hwd : ∀ t, HasDerivAt w ((qu t - qh t) * u t * h t) t := by
    intro t
    have h1 := ((hu' t).mul (hh t)).sub ((hu t).mul (hh' t))
    convert h1 using 1 <;> first | rfl | ring
  have hint : (∫ t in p..r, (qu t - qh t) * u t * h t) = w r - w p :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hwd t)
      ((((hqu.sub hqh).mul huc).mul hhc).intervalIntegrable p r)
  have hposI : 0 < ∫ t in p..r, (qu t - qh t) * u t * h t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((((hqu.sub hqh).mul huc).mul hhc).intervalIntegrable p r)
      (fun t ht => mul_pos (mul_pos (sub_pos.mpr (hlt t ht)) (hupos t ht)) (hhpos t ht)) hpr
  have hd0 : 0 ≤ u' p := deriv_nonneg_of_zero_of_pos_right hpr (hu p) hup hupos
  have hd1 : u' r ≤ 0 := deriv_nonpos_of_zero_of_pos_left hpr (hu r) hur hupos
  have hh0 : 0 ≤ h p := nonneg_left_of_pos_Ioo hpr hhc.continuousAt hhpos
  have hh1 : 0 ≤ h r := nonneg_right_of_pos_Ioo hpr hhc.continuousAt hhpos
  have hwp : 0 ≤ w p := by
    simp only [hw, hup, zero_mul, sub_zero]
    exact mul_nonneg hd0 hh0
  have hwr : w r ≤ 0 := by
    simp only [hw, hur, zero_mul, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg hd1 hh1
  linarith

end UnforcedLeray.ComplexODE
