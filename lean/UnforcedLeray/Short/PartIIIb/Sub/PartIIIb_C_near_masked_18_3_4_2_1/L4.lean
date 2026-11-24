import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4_2_1

/-!
# `sepRadialMajorantIntegrable` (`PartIII-b:C/near/masked/18/3/4/2/1/4`)

Source 3611-3621.  The majorant `l^{2μ+2} 1_S(z) ((|y - l z|² + ν(1-l²))²)⁻¹` is integrable on
`(0,1) × ℝ³`.  Route: the radial integral `∫_x ((|x|²+t)²)⁻¹ dx = (√t)⁻¹ G` (parabolic scaling),
the translation and dilation `z ↦ y - l z` (`dz = l⁻³ dx`), and the bound
`∫_z 1_S(z) F_t(y - l z) ≤ C (1-l)^{-1/2}` on `(0,1)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open MeasureTheory Set Filter UnforcedLeray.Axi
open UnforcedLeray.Short.PartIIIb.Concrete (sepRho)

/-- The radial profile `g(u) = ((|u|²+1)²)⁻¹` on `ℝ³`. -/
def radG (u : Space) : ℝ := ((‖u‖ ^ 2 + 1) ^ 2)⁻¹

lemma radG_nonneg (u : Space) : 0 ≤ radG u := by
  unfold radG
  positivity

lemma radG_integrable : Integrable radG := by
  have hint : Integrable (fun u : Space => (1 + ‖u‖) ^ (-(4 : ℝ))) := by
    apply integrable_one_add_norm
    rw [finrank_euclideanSpace_fin]
    norm_num
  refine Integrable.mono' (hint.const_mul 4) ?_ ?_
  · have hm : Measurable radG := by
      unfold radG
      exact (((measurable_norm.pow_const 2).add_const 1).pow_const 2).inv
    exact hm.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u => ?_
    have h0 : 0 < (1 + ‖u‖) := by positivity
    have hp : (1 + ‖u‖) ^ (-(4 : ℝ)) = ((1 + ‖u‖) ^ 4)⁻¹ := by
      rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg h0.le, Real.rpow_natCast]
    rw [hp, Real.norm_of_nonneg (radG_nonneg u)]
    have hq : (1 + ‖u‖) ^ 4 ≤ 4 * (‖u‖ ^ 2 + 1) ^ 2 := by
      nlinarith [sq_nonneg (‖u‖ - 1), norm_nonneg u]
    have hpos : 0 < (1 + ‖u‖) ^ 4 := by positivity
    have h1 := inv_anti₀ (by positivity) hq
    have h4 : ((‖u‖ ^ 2 + 1) ^ 2)⁻¹ = 4 * (4 * (‖u‖ ^ 2 + 1) ^ 2)⁻¹ := by
      rw [mul_inv]; ring
    unfold radG
    linarith [h1, h4]

/-- Parabolic scaling of the radial profile: `((|x|²+t)²)⁻¹ = t⁻² g(x/√t)`. -/
lemma scale_eq {t : ℝ} (ht : 0 < t) (x : Space) :
    ((‖x‖ ^ 2 + t) ^ 2)⁻¹ = (t ^ 2)⁻¹ * radG ((Real.sqrt t)⁻¹ • x) := by
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  unfold radG
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hsq)]
  have key : ((Real.sqrt t)⁻¹ * ‖x‖) ^ 2 + 1 = (‖x‖ ^ 2 + t) / t := by
    rw [mul_pow, inv_pow, hs2]
    field_simp
  rw [key]
  field_simp

lemma F_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Space => ((‖x‖ ^ 2 + t) ^ 2)⁻¹) := by
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hc : (Real.sqrt t)⁻¹ ≠ 0 := (inv_pos.2 hsq).ne'
  have h := (radG_integrable.comp_smul hc).const_mul ((t ^ 2)⁻¹)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [scale_eq ht x]

lemma F_integral {t : ℝ} (ht : 0 < t) :
    ∫ x : Space, ((‖x‖ ^ 2 + t) ^ 2)⁻¹ = (Real.sqrt t)⁻¹ * ∫ u : Space, radG u := by
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hfun : (fun x : Space => ((‖x‖ ^ 2 + t) ^ 2)⁻¹)
      = fun x : Space => (t ^ 2)⁻¹ * radG ((Real.sqrt t)⁻¹ • x) :=
    funext fun x => scale_eq ht x
  rw [hfun, integral_const_mul, MeasureTheory.Measure.integral_comp_smul volume radG (Real.sqrt t)⁻¹,
    finrank_euclideanSpace_fin]
  rw [smul_eq_mul, abs_of_pos (by positivity)]
  have hc : (t ^ 2)⁻¹ * ((((Real.sqrt t)⁻¹) ^ 3)⁻¹) = (Real.sqrt t)⁻¹ := by
    rw [inv_pow, inv_inv]
    field_simp
    nlinarith [hs2]
  calc (t ^ 2)⁻¹ * ((((Real.sqrt t)⁻¹) ^ 3)⁻¹ * ∫ u : Space, radG u)
      = ((t ^ 2)⁻¹ * ((((Real.sqrt t)⁻¹) ^ 3)⁻¹)) * ∫ u : Space, radG u := by ring
    _ = (Real.sqrt t)⁻¹ * ∫ u : Space, radG u := by rw [hc]

lemma zF_integrable {t : ℝ} (ht : 0 < t) (y : Space) {l : ℝ} (hl : 0 < l) :
    Integrable (fun z : Space => ((‖y - l • z‖ ^ 2 + t) ^ 2)⁻¹) := by
  have hH : Integrable (fun x : Space => ((‖y - x‖ ^ 2 + t) ^ 2)⁻¹) :=
    (F_integrable ht).comp_sub_left y
  exact hH.comp_smul hl.ne'

lemma zF_integral {t : ℝ} (ht : 0 < t) (y : Space) {l : ℝ} (hl : 0 < l) :
    ∫ z : Space, ((‖y - l • z‖ ^ 2 + t) ^ 2)⁻¹
      = (l ^ 3)⁻¹ * ((Real.sqrt t)⁻¹ * ∫ u : Space, radG u) := by
  have h1 := MeasureTheory.Measure.integral_comp_smul volume
    (fun x : Space => ((‖y - x‖ ^ 2 + t) ^ 2)⁻¹) l
  rw [finrank_euclideanSpace_fin] at h1
  have h2 : ∫ x : Space, ((‖y - x‖ ^ 2 + t) ^ 2)⁻¹ = ∫ x : Space, ((‖x‖ ^ 2 + t) ^ 2)⁻¹ :=
    integral_sub_left_eq_self (fun x : Space => ((‖x‖ ^ 2 + t) ^ 2)⁻¹) volume y
  change ∫ z : Space, ((‖y - l • z‖ ^ 2 + t) ^ 2)⁻¹ = _
  rw [h1, smul_eq_mul, h2, F_integral ht, abs_of_pos (by positivity)]

/-- Dominating constant for the `z`-integral of the majorant. -/
def majC (ν : ℝ) (S : Set Space) : ℝ :=
  (volume S).toReal * ((3 * ν / 4) ^ 2)⁻¹ + 8 * (∫ u : Space, radG u) * (Real.sqrt ν)⁻¹

lemma inv_sqrt_bound {ν l : ℝ} (hν : 0 < ν) (hl0 : 0 < l) (hl1 : l < 1) :
    (Real.sqrt (ν * (1 - l ^ 2)))⁻¹ ≤ (Real.sqrt ν)⁻¹ * (1 - l) ^ (-(1 / 2 : ℝ)) := by
  have h1l : 0 < 1 - l := by linarith
  have hpow : (1 - l) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (1 - l))⁻¹ := by
    rw [Real.rpow_neg h1l.le, Real.sqrt_eq_rpow]
  rw [hpow, Real.sqrt_mul hν.le, mul_inv]
  have hs : 0 < Real.sqrt (1 - l) := Real.sqrt_pos.2 h1l
  have hle : Real.sqrt (1 - l) ≤ Real.sqrt (1 - l ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hs hle) (inv_nonneg.2 (Real.sqrt_nonneg _))

lemma majC_nonneg (ν : ℝ) (hν : 0 < ν) (S : Set Space) : 0 ≤ majC ν S := by
  unfold majC
  have h1 : 0 ≤ (volume S).toReal := ENNReal.toReal_nonneg
  have h2 : 0 ≤ ((3 * ν / 4) ^ 2)⁻¹ := by positivity
  have h3 : 0 ≤ ∫ u : Space, radG u := integral_nonneg radG_nonneg
  have h4 : 0 ≤ (Real.sqrt ν)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have := mul_nonneg h1 h2
  have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) h3) h4
  linarith

/-- The `z`-integral of the majorant at a fixed `l ∈ (0,1)`, with `t = ν(1-l²)`. -/
lemma J_bound {ν : ℝ} (S : Set Space) (hS : IsCompact S) (y : Space) (hν : 0 < ν)
    {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) :
    ∫ z : Space, S.indicator (fun z => ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹) z
      ≤ majC ν S * (1 - l) ^ (-(1 / 2 : ℝ)) := by
  have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν (by nlinarith)
  have hr0 : 0 ≤ (1 - l) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hA0 := majC_nonneg ν hν S
  have hind0 : ∀ z : Space, 0 ≤ S.indicator (fun z => ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹) z :=
    fun z => Set.indicator_nonneg (fun _ _ => by positivity) z
  by_cases hcase : l ≤ 1 / 2
  · -- small `l`: the kernel is bounded by `((3ν/4)²)⁻¹` on `S`
    have hM : ∀ x : Space, ((‖x‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹ ≤ ((3 * ν / 4) ^ 2)⁻¹ := by
      intro x
      have hl2 : l ^ 2 ≤ 1 / 4 := by nlinarith
      have hge : 3 * ν / 4 ≤ ν * (1 - l ^ 2) := by nlinarith [mul_le_mul_of_nonneg_left hl2 hν.le]
      have h1 : (3 * ν / 4) ^ 2 ≤ (‖x‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2 := by
        nlinarith [sq_nonneg ‖x‖, norm_nonneg x]
      exact inv_anti₀ (by positivity) h1
    have hfun : ∀ z : Space, S.indicator (fun z => ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹) z
        ≤ S.indicator (fun _ => ((3 * ν / 4) ^ 2)⁻¹) z := by
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        exact hM _
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    have hint : Integrable (S.indicator (fun _ : Space => ((3 * ν / 4) ^ 2)⁻¹)) :=
      ((integrableOn_const (C := ((3 * ν / 4) ^ 2)⁻¹) hS.measure_lt_top.ne)).integrable_indicator
        hS.measurableSet
    have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall hind0) hint
      (Filter.Eventually.of_forall hfun)
    rw [integral_indicator_const _ hS.measurableSet, smul_eq_mul] at hmono
    have hr1 : 1 ≤ (1 - l) ^ (-(1 / 2 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) (by norm_num)
    have hsm : (volume S).toReal * ((3 * ν / 4) ^ 2)⁻¹ ≤ majC ν S := by
      unfold majC
      have h3 : 0 ≤ 8 * (∫ u : Space, radG u) * (Real.sqrt ν)⁻¹ := by
        have h3a : 0 ≤ ∫ u : Space, radG u := integral_nonneg radG_nonneg
        have h3b : 0 ≤ (Real.sqrt ν)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
        positivity
      linarith
    calc ∫ z : Space, S.indicator (fun z => ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹) z
        ≤ (volume S).toReal * ((3 * ν / 4) ^ 2)⁻¹ := hmono
      _ ≤ majC ν S := hsm
      _ = majC ν S * 1 := (mul_one _).symm
      _ ≤ majC ν S * (1 - l) ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hr1 hA0
  · -- large `l`: change of variables `z ↦ y - l z`
    push_neg at hcase
    have hpt : ∀ z : Space, S.indicator (fun z => ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹) z
        ≤ ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹ := by
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        exact (inv_nonneg.2 (by positivity))
    have hsub := integral_mono_of_nonneg (Filter.Eventually.of_forall hind0)
      (zF_integrable ht y hl0) (Filter.Eventually.of_forall hpt)
    rw [zF_integral ht y hl0] at hsub
    have hl3 : (8 : ℝ)⁻¹ ≤ l ^ 3 := by
      have : (1 / 2 : ℝ) ^ 3 ≤ l ^ 3 := pow_le_pow_left₀ (by norm_num) hcase.le 3
      norm_num at this ⊢
      linarith
    have h3 : (l ^ 3)⁻¹ ≤ 8 := inv_le_of_inv_le₀ (by norm_num) hl3
    have hG0 : 0 ≤ ∫ u : Space, radG u := integral_nonneg radG_nonneg
    have hsq := inv_sqrt_bound hν hl0 hl1
    have hsq0 : 0 ≤ (Real.sqrt (ν * (1 - l ^ 2)))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    have hstep : (Real.sqrt (ν * (1 - l ^ 2)))⁻¹ * (∫ u : Space, radG u)
        ≤ (Real.sqrt ν)⁻¹ * (1 - l) ^ (-(1 / 2 : ℝ)) * (∫ u : Space, radG u) :=
      mul_le_mul_of_nonneg_right hsq hG0
    have hinv3 : (l ^ 3)⁻¹ * ((Real.sqrt (ν * (1 - l ^ 2)))⁻¹ * (∫ u : Space, radG u))
        ≤ 8 * ((Real.sqrt ν)⁻¹ * (1 - l) ^ (-(1 / 2 : ℝ)) * (∫ u : Space, radG u)) :=
      mul_le_mul h3 hstep (mul_nonneg hsq0 hG0) (by norm_num)
    have hfin : 8 * ((Real.sqrt ν)⁻¹ * (1 - l) ^ (-(1 / 2 : ℝ)) * (∫ u : Space, radG u))
        ≤ majC ν S * (1 - l) ^ (-(1 / 2 : ℝ)) := by
      unfold majC
      have hvol : 0 ≤ (volume S).toReal * ((3 * ν / 4) ^ 2)⁻¹ := by
        have : 0 ≤ (volume S).toReal := ENNReal.toReal_nonneg
        positivity
      have : 8 * ((Real.sqrt ν)⁻¹ * (1 - l) ^ (-(1 / 2 : ℝ)) * (∫ u : Space, radG u))
          = (8 * (∫ u : Space, radG u) * (Real.sqrt ν)⁻¹) * (1 - l) ^ (-(1 / 2 : ℝ)) := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_right _ hr0
      linarith
    linarith [hsub, hinv3, hfin]

theorem sepRadialMajorantIntegrable :
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SepRadialMajorantIntegrable := by
  intro ν μ S y hν hμ hS
  set f : ℝ × Space → ℝ := fun p => p.1 ^ (2 * μ + 2) * S.indicator (fun _ => (1 : ℝ)) p.2 *
      ((‖y - p.1 • p.2‖ ^ 2 + ν * (1 - p.1 ^ 2)) ^ 2)⁻¹ with hf
  have hfm : Measurable f := by
    rw [hf]
    apply Measurable.mul
    · apply Measurable.mul
      · exact measurable_fst.pow_const _
      · exact (measurable_const.indicator hS.measurableSet).comp measurable_snd
    · exact (((((measurable_norm.comp (measurable_const.sub (measurable_fst.smul measurable_snd)))).pow_const 2).add
        (measurable_const.mul (measurable_const.sub (measurable_fst.pow_const 2)))).pow_const 2).inv
  have hind0 : ∀ (l : ℝ) (z : Space), 0 ≤ S.indicator (fun z : Space =>
      ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹) z :=
    fun l z => Set.indicator_nonneg (fun _ _ => by positivity) z
  have hfeq : ∀ (l : ℝ) (z : Space), f (l, z) = l ^ (2 * μ + 2) * S.indicator (fun z : Space =>
      ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹) z := by
    intro l z
    by_cases hz : z ∈ S
    · simp [hf, Set.indicator_of_mem hz]
    · simp [hf, Set.indicator_of_notMem hz]
  have hrp : IntegrableOn (fun l : ℝ => (1 - l) ^ (-(1 / 2 : ℝ))) (Set.Ioo 0 1) := by
    have h0 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) MeasureTheory.volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have h1 := h0.comp_sub_left 1
    have h2 : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-(1 / 2 : ℝ))) MeasureTheory.volume 0 1 := by
      simpa using h1.symm
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h2
  unfold sepRho
  rw [integrable_prod_iff hfm.aestronglyMeasurable]
  constructor
  · rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun l hl => ?_
    obtain ⟨hl0, hl1⟩ := hl
    have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν (by nlinarith)
    have hind : Integrable (S.indicator (fun z : Space =>
        ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹)) :=
      (zF_integrable ht y hl0).indicator hS.measurableSet
    refine (hind.const_mul (l ^ (2 * μ + 2))).congr (Filter.Eventually.of_forall fun z => ?_)
    exact (hfeq l z).symm
  · have hmeas_int : AEStronglyMeasurable (fun l : ℝ => ∫ z : Space, ‖f (l, z)‖)
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      (hfm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    refine Integrable.mono' (hrp.const_mul (majC ν S)) hmeas_int ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun l hl => ?_
    obtain ⟨hl0, hl1⟩ := hl
    rw [Real.norm_of_nonneg (integral_nonneg fun z => norm_nonneg _)]
    have hnorm : ∀ z : Space, ‖f (l, z)‖ = l ^ (2 * μ + 2) * S.indicator (fun z : Space =>
        ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹) z := by
      intro z
      rw [hfeq l z, Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hl0.le _) (hind0 l z))]
    have hsplit : ∫ z : Space, ‖f (l, z)‖ = l ^ (2 * μ + 2) * ∫ z : Space,
        S.indicator (fun z : Space => ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹) z := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall hnorm)
    rw [hsplit]
    have ha1 : l ^ (2 * μ + 2) ≤ 1 := Real.rpow_le_one hl0.le hl1.le (by linarith)
    have hJ0 : 0 ≤ ∫ z : Space, S.indicator (fun z : Space =>
        ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹) z :=
      integral_nonneg fun z => hind0 l z
    have hJ := J_bound S hS y hν hl0 hl1
    calc l ^ (2 * μ + 2) * ∫ z : Space, S.indicator (fun z : Space =>
            ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹) z
        ≤ 1 * ∫ z : Space, S.indicator (fun z : Space =>
            ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹) z :=
          mul_le_mul_of_nonneg_right ha1 hJ0
      _ = ∫ z : Space, S.indicator (fun z : Space =>
            ((‖y - l • z‖ ^ 2 + ν * (1 - l ^ 2)) ^ 2)⁻¹) z := one_mul _
      _ ≤ majC ν S * (1 - l) ^ (-(1 / 2 : ℝ)) := hJ

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
