import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.FlatGraphOrg

/-!
Leaf `PartII-b:T13/1/6` (SP 1931): comparability of `s^{r/2-5/2}` on each window.

On a measurable `E ⊆ [a/2, 4a] × ℝ²` the slice formula for `ageμ` and the unweighted cylinder
measure differ by the weight `s^κ`, which is comparable to `a^κ` on `[a/2, 4a]` for
`κ = r/2 - 5/2 ∈ [-2, 0]`. The `eLpNorm` scaling `‖f‖_{p, c•μ} = c^{1/p} ‖f‖_{p, μ}` then gives
both inequalities.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

/-- Slice formula for `ageμ`: `ageμ c κ E = ∫ ρ(E_x) s^κ ds` over `s > 0`. -/
theorem wwc_ageμ_apply (c κ : ℝ) {E : Set Coord} (hE : MeasurableSet E) :
    Axi.ageμ c κ E = ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) *
      ENNReal.ofReal (x ^ κ) ∂((volume : Measure ℝ).restrict (Ioi 0)) := by
  unfold Axi.ageμ
  rw [Measure.prod_apply hE,
    lintegral_withDensity_eq_lintegral_mul _ (Axi.measurable_ofReal_rpow κ)
      (measurable_measure_prodMk_left hE)]
  exact lintegral_congr fun x => by simp only [Pi.mul_apply]; exact mul_comm _ _

/-- Slice formula for the unweighted cylinder measure. -/
theorem wwc_cyl_apply (c : ℝ) {E : Set Coord} (hE : MeasurableSet E) :
    cylMeas c E = ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) ∂(volume : Measure ℝ) := by
  unfold cylMeas
  rw [Measure.prod_apply hE]

/-- Slices of a set in `winSet2 a` vanish outside `[a/2, 4a]`. -/
theorem wwc_slice_empty (c a : ℝ) {E : Set Coord} (hsub : E ⊆ winSet2 a) {x : ℝ}
    (hx : x ∉ Icc (a / 2) (4 * a)) : (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) = 0 := by
  have h : Prod.mk x ⁻¹' E = ∅ := by
    ext z
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    intro hz
    have h2 := hsub hz
    simp only [winSet2, mem_prod] at h2
    exact hx h2.1
  rw [h, measure_empty]

theorem wwc_rpow_two_neg : (2:ℝ) ^ (-2:ℝ) = 1 / 4 := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num

theorem wwc_rpow_four_neg : (4:ℝ) ^ (-2:ℝ) = 1 / 16 := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num

/-- Upper weight bound on the window: `x^κ ≤ 4 a^κ` for `x ∈ [a/2, 4a]`. -/
theorem wwc_upper {a κ x : ℝ} (ha : 0 < a) (hκ2 : -2 ≤ κ) (hκ0 : κ ≤ 0)
    (hx : x ∈ Icc (a / 2) (4 * a)) : x ^ κ ≤ 4 * a ^ κ := by
  have hx0 : 0 < a / 2 := half_pos ha
  have h1 : x ^ κ ≤ (a / 2) ^ κ := Real.rpow_le_rpow_of_nonpos hx0 hx.1 hκ0
  have h2 : (1 / 4 : ℝ) ≤ (2:ℝ) ^ κ := by
    rw [← wwc_rpow_two_neg]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hκ2
  rw [Real.div_rpow ha.le (by norm_num : (0:ℝ) ≤ 2)] at h1
  have hpos : 0 < (2:ℝ) ^ κ := Real.rpow_pos_of_pos (by norm_num) κ
  have hA : 0 ≤ a ^ κ := Real.rpow_nonneg ha.le κ
  calc x ^ κ ≤ a ^ κ / 2 ^ κ := h1
    _ ≤ 4 * a ^ κ := by
      rw [div_le_iff₀ hpos]
      nlinarith [mul_nonneg hA (sub_nonneg.2 h2)]

/-- Lower weight bound on the window: `a^κ ≤ 16 x^κ` for `x ∈ [a/2, 4a]`. -/
theorem wwc_lower {a κ x : ℝ} (ha : 0 < a) (hκ2 : -2 ≤ κ) (hκ0 : κ ≤ 0)
    (hx : x ∈ Icc (a / 2) (4 * a)) : a ^ κ ≤ 16 * x ^ κ := by
  have hx0 : 0 < x := lt_of_lt_of_le (half_pos ha) hx.1
  have h1 : (4 * a) ^ κ ≤ x ^ κ := Real.rpow_le_rpow_of_nonpos hx0 hx.2 hκ0
  have h2 : (1 / 16 : ℝ) ≤ (4:ℝ) ^ κ := by
    rw [← wwc_rpow_four_neg]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hκ2
  rw [Real.mul_rpow (by norm_num) ha.le] at h1
  have hA : 0 ≤ a ^ κ := Real.rpow_nonneg ha.le κ
  nlinarith [mul_nonneg hA (sub_nonneg.2 h2)]

/-- The slice integral bound `ageμ ≤ 4a^κ · cylMeas` on sets of the window. -/
theorem wwc_ageμ_le {a κ c : ℝ} (ha : 0 < a) (hκ2 : -2 ≤ κ) (hκ0 : κ ≤ 0) {E : Set Coord}
    (hE : MeasurableSet E) (hsub : E ⊆ winSet2 a) :
    Axi.ageμ c κ E ≤ ENNReal.ofReal (4 * a ^ κ) * cylMeas c E := by
  rw [wwc_ageμ_apply c κ hE, wwc_cyl_apply c hE]
  calc ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) * ENNReal.ofReal (x ^ κ)
        ∂((volume : Measure ℝ).restrict (Ioi 0))
      ≤ ∫⁻ x, ENNReal.ofReal (4 * a ^ κ) * (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E)
        ∂((volume : Measure ℝ).restrict (Ioi 0)) := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Icc (a / 2) (4 * a)
        · calc (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) * ENNReal.ofReal (x ^ κ)
              ≤ (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) * ENNReal.ofReal (4 * a ^ κ) :=
                by
                  have h' := ENNReal.ofReal_le_ofReal (wwc_upper ha hκ2 hκ0 hx)
                  gcongr
            _ = ENNReal.ofReal (4 * a ^ κ) * (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) :=
                mul_comm _ _
        · rw [wwc_slice_empty c a hsub hx]; simp
    _ = ENNReal.ofReal (4 * a ^ κ) * ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E)
        ∂((volume : Measure ℝ).restrict (Ioi 0)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (4 * a ^ κ) * ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E)
        ∂(volume : Measure ℝ) :=
        by
          have hm : ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E)
              ∂((volume : Measure ℝ).restrict (Ioi 0)) ≤
              ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) ∂(volume : Measure ℝ) :=
            lintegral_mono' Measure.restrict_le_self le_rfl
          gcongr

/-- The reverse slice bound `a^κ · cylMeas ≤ 16 · ageμ` on sets of the window. -/
theorem wwc_cyl_le_ageμ {a κ c : ℝ} (ha : 0 < a) (hκ2 : -2 ≤ κ) (hκ0 : κ ≤ 0) {E : Set Coord}
    (hE : MeasurableSet E) (hsub : E ⊆ winSet2 a) :
    ENNReal.ofReal (a ^ κ) * cylMeas c E ≤ 16 * Axi.ageμ c κ E := by
  have hsupp : Function.support (fun x => (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E)) ⊆
      Ioi (0:ℝ) := by
    intro x hx
    have hxI : x ∈ Icc (a / 2) (4 * a) := by
      by_contra h'
      exact hx (wwc_slice_empty c a hsub h')
    exact lt_of_lt_of_le (half_pos ha) hxI.1
  have hEq : ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) ∂(volume : Measure ℝ) =
      ∫⁻ x in Ioi (0:ℝ), (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) ∂(volume : Measure ℝ) :=
    (setLIntegral_eq_of_support_subset hsupp).symm
  rw [wwc_ageμ_apply c κ hE, wwc_cyl_apply c hE, hEq]
  calc ENNReal.ofReal (a ^ κ) *
        ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) ∂((volume : Measure ℝ).restrict (Ioi 0))
      = ∫⁻ x, ENNReal.ofReal (a ^ κ) * (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E)
        ∂((volume : Measure ℝ).restrict (Ioi 0)) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ x, 16 * ((UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) * ENNReal.ofReal (x ^ κ))
        ∂((volume : Measure ℝ).restrict (Ioi 0)) := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Icc (a / 2) (4 * a)
        · have h16 : ENNReal.ofReal (a ^ κ) ≤ 16 * ENNReal.ofReal (x ^ κ) := by
            calc ENNReal.ofReal (a ^ κ) ≤ ENNReal.ofReal (16 * x ^ κ) :=
                  ENNReal.ofReal_le_ofReal (wwc_lower ha hκ2 hκ0 hx)
              _ = 16 * ENNReal.ofReal (x ^ κ) := by
                  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          calc ENNReal.ofReal (a ^ κ) * (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E)
              ≤ (16 * ENNReal.ofReal (x ^ κ)) * (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) :=
                by gcongr
            _ = 16 * ((UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) * ENNReal.ofReal (x ^ κ)) := by
                ring
        · rw [wwc_slice_empty c a hsub hx]; simp
    _ = 16 * ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) * ENNReal.ofReal (x ^ κ)
        ∂((volume : Measure ℝ).restrict (Ioi 0)) :=
        lintegral_const_mul' _ _ (by norm_num)

/-- Measure comparison on the window, first direction. -/
theorem wwc_measure_le {a κ c : ℝ} (ha : 0 < a) (hκ2 : -2 ≤ κ) (hκ0 : κ ≤ 0) {A : Set Coord}
    (hA : MeasurableSet A) (hsub : A ⊆ winSet2 a) :
    (Axi.ageμ c κ).restrict A ≤ ENNReal.ofReal (4 * a ^ κ) • (cylMeas c).restrict A := by
  rw [Measure.le_iff]
  intro B hB
  simp only [Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul]
  exact wwc_ageμ_le ha hκ2 hκ0 (hB.inter hA) (fun z hz => hsub hz.2)

/-- Measure comparison on the window, second direction. -/
theorem wwc_measure_ge {a κ c : ℝ} (ha : 0 < a) (hκ2 : -2 ≤ κ) (hκ0 : κ ≤ 0) {A : Set Coord}
    (hA : MeasurableSet A) (hsub : A ⊆ winSet2 a) :
    ENNReal.ofReal (a ^ κ) • (cylMeas c).restrict A ≤
      (16 : ℝ≥0∞) • (Axi.ageμ c κ).restrict A := by
  rw [Measure.le_iff]
  intro B hB
  simp only [Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul]
  exact wwc_cyl_le_ageμ ha hκ2 hκ0 (hB.inter hA) (fun z hz => hsub hz.2)

theorem wwc_pow_div (a κ r : ℝ) (ha : 0 < a) : (a ^ κ) ^ (1 / r) = a ^ (κ / r) := by
  rw [← Real.rpow_mul ha.le]
  congr 1
  ring

theorem wwc_real1 {a r : ℝ} (ha : 0 < a) (hr1 : 1 < r) :
    (4 * a ^ (r / 2 - 5 / 2)) ^ (1 / r) ≤ 16 * a ^ ((r / 2 - 5 / 2) / r) := by
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg ha.le _), wwc_pow_div a _ r ha]
  have h4 : (4:ℝ) ^ (1 / r) ≤ 4 := by
    calc (4:ℝ) ^ (1 / r) ≤ 4 ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by rw [div_le_one (by linarith : (0:ℝ) < r)]; linarith)
      _ = 4 := Real.rpow_one 4
  have hX : 0 ≤ a ^ ((r / 2 - 5 / 2) / r) := Real.rpow_nonneg ha.le _
  have := mul_le_mul_of_nonneg_right h4 hX
  linarith

/-- **Leaf `PartII-b:T13/1/6`** (SP 1931): comparability of `s^{r/2-5/2}` on each window. -/
theorem windowWeightCompare : WindowWeightCompare := by
  intro c r a hc hr1 hr3 ha A hA hsub f hf
  unfold hNormOn hMeas
  have hκ2 : (-2 : ℝ) ≤ r / 2 - 5 / 2 := by linarith
  have hκ0 : r / 2 - 5 / 2 ≤ 0 := by linarith
  have hr0 : (0:ℝ) ≤ r := by linarith
  have hp : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpinv : (1 / ENNReal.ofReal r).toReal = 1 / r := by
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hr0, one_div]
  have hle1 : 1 / r ≤ (1:ℝ) := by
    rw [div_le_one (by linarith : (0:ℝ) < r)]; linarith
  constructor
  · have h1 := eLpNorm_mono_measure (p := ENNReal.ofReal r) f
      (wwc_measure_le (c := c) ha hκ2 hκ0 hA hsub)
    refine h1.trans ?_
    rw [eLpNorm_smul_measure_of_ne_top hp, hpinv, smul_eq_mul,
      ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (by norm_num) (Real.rpow_nonneg ha.le _)) (by positivity)]
    have hh := ENNReal.ofReal_le_ofReal (wwc_real1 ha hr1)
    gcongr
  · have h2 := wwc_measure_ge (c := c) ha hκ2 hκ0 hA hsub
    have h3 := eLpNorm_mono_measure (p := ENNReal.ofReal r) f h2
    have h16 : (16 : ℝ≥0∞) ^ (1 / r) ≤ 16 := by
      calc (16 : ℝ≥0∞) ^ (1 / r) ≤ (16 : ℝ≥0∞) ^ (1:ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hle1
        _ = 16 := ENNReal.rpow_one 16
    calc ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm f (ENNReal.ofReal r) ((cylMeas c).restrict A)
        = eLpNorm f (ENNReal.ofReal r)
            (ENNReal.ofReal (a ^ (r / 2 - 5 / 2)) • (cylMeas c).restrict A) := by
          rw [eLpNorm_smul_measure_of_ne_top hp, hpinv, smul_eq_mul,
            ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ha.le _) (by positivity),
            wwc_pow_div a _ r ha]
      _ ≤ eLpNorm f (ENNReal.ofReal r)
            ((16 : ℝ≥0∞) • (Axi.ageμ c (r / 2 - 5 / 2)).restrict A) := h3
      _ = (16 : ℝ≥0∞) ^ (1 / r) *
            eLpNorm f (ENNReal.ofReal r) ((Axi.ageμ c (r / 2 - 5 / 2)).restrict A) := by
          rw [eLpNorm_smul_measure_of_ne_top hp, hpinv, smul_eq_mul]
      _ ≤ 16 * eLpNorm f (ENNReal.ofReal r) ((Axi.ageμ c (r / 2 - 5 / 2)).restrict A) := by
          gcongr

end UnforcedLeray.Short.IIb
