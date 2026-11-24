import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_3

/-!
# Part III-a, task `PartIII-a:T21/2/3/3/2`: dilation of the weighted `L²` norm (SP 3044)

For `a > 0`, `s = √a`, the substitution `x = s y` maps the cell of length `c` to the cell of
length `c/s` and the weight `⟨x⟩^{-2m}` is comparable, up to a constant depending only on
`m` and `a`, to its value at the dilated point (`jb(s y)` lies between `min(1,a) jb(y)` and
`max(1,a) jb(y)`). The Lebesgue change of variables `y ↦ s • y` in the plane gives the
factor `a⁻¹`, so `‖y ↦ K f(s y)‖_{L²(cellMeasure (c/s) (-m))} < ∞` whenever
`f ∈ L²(cellMeasure c (-m))`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff NNReal

namespace UnforcedLeray.Short.IIIa

/-- The comparison constant `min(1,a)^m + max(1,a)^m`. -/
def mpM (m a : ℝ) : ℝ := (min 1 a) ^ m + (max 1 a) ^ m

lemma mpM_nonneg (m a : ℝ) (ha : 0 < a) : 0 ≤ mpM m a :=
  add_nonneg (Real.rpow_nonneg (lt_min one_pos ha).le _)
    (Real.rpow_nonneg (lt_max_of_lt_left one_pos).le _)

/-- Real comparison of the weights at `y` and at the dilated point `(√a y₁, √a y₂)`. -/
lemma mpJbRatio (m a : ℝ) (ha : 0 < a) (y : ℝ × ℝ) :
    B0579.jb y ^ (-m) ≤ mpM m a * B0579.jb (Real.sqrt a * y.1, Real.sqrt a * y.2) ^ (-m) := by
  unfold mpM
  set u := B0579.jb y with hu_def
  set v := B0579.jb (Real.sqrt a * y.1, Real.sqrt a * y.2) with hv_def
  have hu : 0 < u := B0579.jb_pos y
  have hv : 0 < v := B0579.jb_pos _
  have hr : 0 ≤ y.1 ^ 2 + y.2 ^ 2 := by positivity
  have huv : u = 1 + (y.1 ^ 2 + y.2 ^ 2) := by
    simp only [hu_def, B0579.jb]; ring
  have hvv : v = 1 + a * (y.1 ^ 2 + y.2 ^ 2) := by
    simp only [hv_def, B0579.jb]
    rw [mul_pow, mul_pow, Real.sq_sqrt ha.le]
    ring
  have hp : 0 < min 1 a := lt_min one_pos ha
  have hq : 0 < max 1 a := lt_max_of_lt_left one_pos
  have hpr : min 1 a * (y.1 ^ 2 + y.2 ^ 2) ≤ a * (y.1 ^ 2 + y.2 ^ 2) :=
    mul_le_mul_of_nonneg_right (min_le_right 1 a) hr
  have hrq : a * (y.1 ^ 2 + y.2 ^ 2) ≤ max 1 a * (y.1 ^ 2 + y.2 ^ 2) :=
    mul_le_mul_of_nonneg_right (le_max_right 1 a) hr
  have hpu : min 1 a ≤ v / u := by
    rw [le_div_iff₀ hu, huv, hvv]
    nlinarith [min_le_left 1 a]
  have hqu : v / u ≤ max 1 a := by
    rw [div_le_iff₀ hu, huv, hvv]
    nlinarith [le_max_left 1 a]
  have hkey : u ^ (-m) = v ^ (-m) * (v / u) ^ m := by
    have h1 : 0 < u ^ m := Real.rpow_pos_of_pos hu m
    have h2 : 0 < v ^ m := Real.rpow_pos_of_pos hv m
    rw [Real.div_rpow hv.le hu.le, Real.rpow_neg hu.le, Real.rpow_neg hv.le]
    field_simp
  have hvm : 0 ≤ v ^ (-m) := Real.rpow_nonneg hv.le _
  have ht : (v / u) ^ m ≤ (min 1 a) ^ m + (max 1 a) ^ m := by
    rcases le_total 0 m with hm | hm
    · have h1 := Real.rpow_le_rpow (div_pos hv hu).le hqu hm
      have h2 : 0 ≤ (min 1 a) ^ m := Real.rpow_nonneg hp.le _
      linarith
    · have h1 := Real.rpow_le_rpow_of_nonpos hp hpu hm
      have h2 : 0 ≤ (max 1 a) ^ m := Real.rpow_nonneg hq.le _
      linarith
  rw [hkey, mul_comm (min 1 a ^ m + max 1 a ^ m)]
  exact mul_le_mul_of_nonneg_left ht hvm

/-- The density comparison in `ℝ≥0∞`. -/
lemma mpDensityLe (m a : ℝ) (ha : 0 < a) (y : ℝ × ℝ) :
    ((B0579.density (-m) y : ℝ≥0) : ℝ≥0∞) ≤
      ENNReal.ofReal (mpM m a) *
        ((B0579.density (-m) (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ≥0) : ℝ≥0∞) := by
  have h := mpJbRatio m a ha y
  have hM : 0 ≤ mpM m a := mpM_nonneg m a ha
  show ENNReal.ofReal (B0579.jb y ^ (-m)) ≤
    ENNReal.ofReal (mpM m a) *
      ENNReal.ofReal (B0579.jb (Real.sqrt a * y.1, Real.sqrt a * y.2) ^ (-m))
  rw [← ENNReal.ofReal_mul hM]
  exact ENNReal.ofReal_le_ofReal h

/-- Lebesgue change of variables for a dilation of the plane, `∫ g(s y) dy = |s²|⁻¹ ∫ g`. -/
lemma mpLintScale (s : ℝ) (hs : 0 < s) (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g (s • y) = ENNReal.ofReal |(s ^ 2)⁻¹| * ∫⁻ x, g x := by
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have hmap := MeasureTheory.Measure.map_addHaar_smul
    (μ := (volume : Measure (ℝ × ℝ))) (r := s) hs.ne'
  rw [hfin] at hmap
  calc ∫⁻ y, g (s • y) = ∫⁻ x, g x ∂(Measure.map (fun y : ℝ × ℝ => s • y) volume) :=
        (lintegral_map hg (measurable_const_smul s)).symm
    _ = ∫⁻ x, g x ∂(ENNReal.ofReal |(s ^ 2)⁻¹| • (volume : Measure (ℝ × ℝ))) := by
        rw [hmap]
    _ = ENNReal.ofReal |(s ^ 2)⁻¹| * ∫⁻ x, g x := by
        rw [lintegral_smul_measure, smul_eq_mul]

/-- The weighted cell integral, written over the whole plane with an indicator. -/
lemma mpLintCell (c m : ℝ) (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂(B0579.cellMeasure c m) =
      ∫⁻ y, (B0579.cell c).indicator (fun y => ((B0579.density m y : ℝ≥0) : ℝ≥0∞) * g y) y := by
  unfold B0579.cellMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _
      (B0579.measurable_density m).coe_nnreal_ennreal hg,
    lintegral_indicator (B0579.measurableSet_cell c)]
  rfl

/-- The integrand of the source norm, cut to the cell. -/
def mpCellG (m c : ℝ) (f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℝ≥0∞ :=
  (B0579.cell c).indicator (fun x => ((B0579.density (-m) x : ℝ≥0) : ℝ≥0∞) * ‖f x‖ₑ ^ 2)

lemma mpCellG_meas (m c : ℝ) {f : ℝ × ℝ → ℂ} (hf : Measurable f) : Measurable (mpCellG m c f) :=
  ((B0579.measurable_density (-m)).coe_nnreal_ennreal.mul (hf.enorm.pow_const 2)).indicator
    (B0579.measurableSet_cell c)

/-- Dilation maps the cell `c/s` into the cell `c`. -/
lemma mpMem_cell (c s : ℝ) (hs : 0 < s) (y : ℝ × ℝ) (hy : y ∈ B0579.cell (c / s)) :
    s • y ∈ B0579.cell c := by
  have hs0 : s ≠ 0 := hs.ne'
  have e : s * (c / s / 2) = c / 2 := by field_simp
  have h1 : -(c / s / 2) ≤ y.1 := hy.1.1
  have h2 : y.1 < c / s / 2 := hy.1.2
  have h3 := mul_le_mul_of_nonneg_left h1 hs.le
  have h4 := mul_lt_mul_of_pos_left h2 hs
  have e2 : s * (-(c / s / 2)) = -(c / 2) := by rw [mul_neg, e]
  unfold B0579.cell
  refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
  · show -(c / 2) ≤ s * y.1
    linarith
  · show s * y.1 < c / 2
    linarith

theorem mpScaleMemLp : MpScaleMemLp := by
  intro m c a hc ha K f hf hfL
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hfc : Continuous fun y : ℝ × ℝ => (K : ℂ) * f (Real.sqrt a * y.1, Real.sqrt a * y.2) :=
    continuous_const.mul (hf.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd)))
  have hfsq : Measurable fun x => ‖f x‖ₑ ^ 2 := (hf.measurable.enorm).pow_const 2
  have hL : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(B0579.cellMeasure c (-m)) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
      ENNReal.ofNat_ne_top).mp hfL.2
    simpa [ENNReal.rpow_two, ENNReal.toReal_ofNat] using h
  have hG : Measurable (mpCellG m c f) := mpCellG_meas m c hf.measurable
  have hGint : ∫⁻ x, mpCellG m c f x = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(B0579.cellMeasure c (-m)) :=
    (mpLintCell c (-m) (fun x => ‖f x‖ₑ ^ 2) hfsq).symm
  have hFsq : Measurable fun y : ℝ × ℝ =>
      ‖(K : ℂ) * f (Real.sqrt a * y.1, Real.sqrt a * y.2)‖ₑ ^ 2 :=
    (hfc.measurable.enorm).pow_const 2
  have hKne : ‖(K : ℂ)‖ₑ ^ 2 < ⊤ := ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr enorm_ne_top)
  have hMc : ENNReal.ofReal (mpM m a) < ⊤ := ENNReal.ofReal_lt_top
  have hA : ENNReal.ofReal (mpM m a) * ‖(K : ℂ)‖ₑ ^ 2 < ⊤ := ENNReal.mul_lt_top hMc hKne
  have hpt : ∀ y : ℝ × ℝ,
      (B0579.cell (c / Real.sqrt a)).indicator
        (fun y => ((B0579.density (-m) y : ℝ≥0) : ℝ≥0∞) *
          ‖(K : ℂ) * f (Real.sqrt a * y.1, Real.sqrt a * y.2)‖ₑ ^ 2) y
      ≤ ENNReal.ofReal (mpM m a) * ‖(K : ℂ)‖ₑ ^ 2 * mpCellG m c f (Real.sqrt a • y) := by
    intro y
    by_cases hy : y ∈ B0579.cell (c / Real.sqrt a)
    · have hmem := mpMem_cell c (Real.sqrt a) hs y hy
      simp only [Set.indicator_of_mem hy, mpCellG, Set.indicator_of_mem hmem]
      have hd := mpDensityLe m a ha y
      have hn : ‖(K : ℂ) * f (Real.sqrt a * y.1, Real.sqrt a * y.2)‖ₑ ^ 2 =
          ‖(K : ℂ)‖ₑ ^ 2 * ‖f (Real.sqrt a * y.1, Real.sqrt a * y.2)‖ₑ ^ 2 := by
        rw [enorm_mul, mul_pow]
      rw [hn]
      have hgen : ∀ A B C D E : ℝ≥0∞, A ≤ B * C → A * (D * E) ≤ B * D * (C * E) := by
        intro A B C D E h
        calc A * (D * E) ≤ (B * C) * (D * E) := by gcongr
          _ = B * D * (C * E) := by ring
      exact hgen _ _ _ _ _ hd
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
  have hfin : ∫⁻ y, mpCellG m c f (Real.sqrt a • y) = ∫⁻ y, mpCellG m c f (Real.sqrt a • y) :=
    rfl
  have hint : ∫⁻ y, ‖(K : ℂ) * f (Real.sqrt a * y.1, Real.sqrt a * y.2)‖ₑ ^ 2
      ∂(B0579.cellMeasure (c / Real.sqrt a) (-m)) < ⊤ := by
    calc ∫⁻ y, ‖(K : ℂ) * f (Real.sqrt a * y.1, Real.sqrt a * y.2)‖ₑ ^ 2
          ∂(B0579.cellMeasure (c / Real.sqrt a) (-m))
        = ∫⁻ y, (B0579.cell (c / Real.sqrt a)).indicator
            (fun y => ((B0579.density (-m) y : ℝ≥0) : ℝ≥0∞) *
              ‖(K : ℂ) * f (Real.sqrt a * y.1, Real.sqrt a * y.2)‖ₑ ^ 2) y :=
          mpLintCell _ _ _ hFsq
      _ ≤ ∫⁻ y, ENNReal.ofReal (mpM m a) * ‖(K : ℂ)‖ₑ ^ 2 * mpCellG m c f (Real.sqrt a • y) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (mpM m a) * ‖(K : ℂ)‖ₑ ^ 2 * ∫⁻ y, mpCellG m c f (Real.sqrt a • y) :=
          lintegral_const_mul' _ _ (ne_of_lt hA)
      _ = ENNReal.ofReal (mpM m a) * ‖(K : ℂ)‖ₑ ^ 2 *
            (ENNReal.ofReal |((Real.sqrt a) ^ 2)⁻¹| * ∫⁻ x, mpCellG m c f x) := by
          rw [mpLintScale (Real.sqrt a) hs (mpCellG m c f) hG]
      _ = ENNReal.ofReal (mpM m a) * ‖(K : ℂ)‖ₑ ^ 2 *
            (ENNReal.ofReal |((Real.sqrt a) ^ 2)⁻¹| *
              ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(B0579.cellMeasure c (-m))) := by
          rw [hGint]
      _ < ⊤ := ENNReal.mul_lt_top hA
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL)
  refine ⟨hfc.aestronglyMeasurable, ?_⟩
  unfold cellLen
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simpa [ENNReal.rpow_two, ENNReal.toReal_ofNat] using hint

end UnforcedLeray.Short.IIIa
