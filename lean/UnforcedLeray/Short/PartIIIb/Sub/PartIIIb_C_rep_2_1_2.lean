import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1
import UnforcedLeray.Lib.ConvIneq.YoungGroup
import UnforcedLeray.Lib.ConvIneq.RadialKernelNorm

/-!
# `PartIII-b:C/rep/2/1/2` : `SepKdYoungScaled` (SP 3624-3645)

(i) `‖sepKd j D‖_{L^b} = C D^{-4-j+3/b}` from `lintegral_gapProfile_norm`;
(ii) dilation `z' = l z`, Jacobian `l^{-3}`; (iii) Young (`eLpNorm_convAbs_le_young`);
(iv) `‖g'(·/l)‖_p = l^{3/p}‖g'‖_p`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sky_lqNorm_eq_eLpNorm {q : ℝ} (hq : 1 ≤ q) (f : Space → ℝ≥0∞) :
    lqNorm q f = eLpNorm f (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hne0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq0).ne'
  have hneT : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 hneT, ENNReal.toReal_ofReal hq0.le]
  simp only [lqNorm, enorm_eq_self]

theorem sky_sepKd_measurable (j : ℕ) (D : ℝ) : Measurable (IIIa.sepKd j D) := by
  unfold IIIa.sepKd
  exact Measurable.ite (measurableSet_le measurable_const measurable_norm)
    (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)) measurable_const

theorem sky_sepKd_ne_top (j : ℕ) (D : ℝ) (x : Space) : IIIa.sepKd j D x ≠ ⊤ := by
  unfold IIIa.sepKd
  split_ifs
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top

/-- (i) the `L^b` norm of the gap kernel. -/
theorem sky_kernel_Lb (j : ℕ) {b : ℝ} (hb : 1 ≤ b) {D : ℝ} (hD : 0 < D) :
    lqNorm b (IIIa.sepKd j D) =
      ENNReal.ofReal ((4 * Real.pi / (((4 + (j : ℝ)) * b) - 3)) ^ (1 / b) *
        D ^ (-4 - (j : ℝ) + 3 / b)) := by
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb
  have hβ : 3 < (4 + (j : ℝ)) * b := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hpt : ∀ x : Space, IIIa.sepKd j D x ^ b =
      ENNReal.ofReal (Conv.gapProfile ((4 + (j : ℝ)) * b) D ‖x‖) := by
    intro x
    unfold IIIa.sepKd Conv.gapProfile
    by_cases h : D ≤ ‖x‖
    · simp only [h, ite_true]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hD.le.trans h) _) hb0.le,
        ← Real.rpow_mul (hD.le.trans h)]
      congr 2
      ring
    · simp only [h, ite_false]
      rw [ENNReal.zero_rpow_of_pos hb0]; simp
  unfold lqNorm
  simp_rw [hpt]
  rw [Conv.lintegral_gapProfile_norm hβ hD]
  have hpos : 0 < (4 + (j : ℝ)) * b - 3 := by linarith
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  congr 1
  rw [show 4 * Real.pi * D ^ (3 - (4 + (j : ℝ)) * b) / ((4 + (j : ℝ)) * b - 3) =
      (4 * Real.pi / ((4 + (j : ℝ)) * b - 3)) * D ^ (3 - (4 + (j : ℝ)) * b) by ring,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hD.le]
  congr 2
  field_simp
  ring

/-- Change of variables under the dilation `z ↦ c z` of `ℝ³`. -/
theorem sky_lintegral_comp_smul {c : ℝ} (hc : c ≠ 0) (H : Space → ℝ≥0∞) :
    ∫⁻ z, H (c • z) = ENNReal.ofReal (|c ^ 3|⁻¹) * ∫⁻ y, H y := by
  have hmap := Measure.map_addHaar_smul (μ := (volume : Measure Space)) hc
  rw [Conv.finrank_space] at hmap
  have h1 := lintegral_map_equiv H (MeasurableEquiv.smul₀ c hc) (μ := (volume : Measure Space))
  have hcoe : (Measure.map (MeasurableEquiv.smul₀ c hc) (volume : Measure Space)) =
      Measure.map (c • ·) (volume : Measure Space) := rfl
  rw [hcoe, hmap, lintegral_smul_measure] at h1
  calc ∫⁻ z, H (c • z) = ∫⁻ a, H ((MeasurableEquiv.smul₀ c hc) a) := rfl
    _ = _ := by rw [← h1, smul_eq_mul, abs_inv]

/-- Constant-factor and dilation scaling of `lqNorm`. -/
theorem sky_lqNorm_dil {q : ℝ} (hq : 0 < q) (f : Space → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    lqNorm q (fun z => f (c • z)) = ENNReal.ofReal (c ^ (-3 / q)) * lqNorm q f := by
  unfold lqNorm
  have h1 : ∫⁻ z : Space, f (c • z) ^ q = ENNReal.ofReal (|c ^ 3|⁻¹) * ∫⁻ y, f y ^ q :=
    sky_lintegral_comp_smul (c := c) hc.ne' (fun y => f y ^ q)
  rw [h1, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  congr 2
  rw [abs_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_neg (by positivity),
    ← Real.rpow_mul hc.le]
  congr 1
  push_cast
  ring

theorem sky_lqNorm_const_mul {q : ℝ} (hq : 0 < q) {a : ℝ≥0∞} (ha : a ≠ ⊤) (f : Space → ℝ≥0∞) :
    lqNorm q (fun y => a * f y) = a * lqNorm q f := by
  unfold lqNorm
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le ha),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hq.ne', ENNReal.rpow_one]

/-- (iii) Young for `ℝ≥0∞`-valued data, finite kernel, `g` of finite norm. -/
theorem sky_young_conv (K g : Space → ℝ≥0∞) (hK : Measurable K) (hKt : ∀ x, K x ≠ ⊤)
    (hg : Measurable g) {b p q : ℝ} (hb : 1 ≤ b) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (h : 1 + 1 / q = 1 / p + 1 / b) (hgt : lqNorm p g ≠ ⊤) :
    lqNorm q (fun y => ∫⁻ x, K (y - x) * g x) ≤ lqNorm b K * lqNorm p g := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hgfin : ∀ᵐ x ∂(volume : Measure Space), g x ≠ ⊤ := by
    have h1 : ∫⁻ x, g x ^ p ≠ ⊤ := by
      intro h0
      apply hgt
      unfold lqNorm
      rw [h0]; exact ENNReal.top_rpow_of_pos (by positivity)
    have h2 : ∀ᵐ x ∂(volume : Measure Space), g x ^ p < ⊤ :=
      ae_lt_top (hg.pow_const p) h1
    filter_upwards [h2] with x hx
    intro hxt
    rw [hxt, ENNReal.top_rpow_of_pos hp0] at hx
    exact absurd hx (lt_irrefl _)
  set K' : Space → ℝ := fun x => (K x).toReal with hK'
  set g' : Space → ℝ := fun x => (g x).toReal with hg'
  have hK'm : AEStronglyMeasurable K' volume := (hK.ennreal_toReal).aestronglyMeasurable
  have hg'm : AEStronglyMeasurable g' volume := (hg.ennreal_toReal).aestronglyMeasurable
  have eK : ∀ x, ‖K' x‖ₑ = K x := by
    intro x
    simp only [hK', Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hKt x)]
  have eg : ∀ᵐ x ∂(volume : Measure Space), ‖g' x‖ₑ = g x := by
    filter_upwards [hgfin] with x hx
    simp only [hg', Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx]
  have hconv : (fun y => ∫⁻ x, K (y - x) * g x) = Conv.convAbs volume K' g' := by
    funext y
    unfold Conv.convAbs
    refine lintegral_congr_ae ?_
    filter_upwards [eg] with x hx
    rw [eK, hx]
  have hnK : lqNorm b K = eLpNorm K' (ENNReal.ofReal b) volume := by
    rw [sky_lqNorm_eq_eLpNorm hb]
    exact (eLpNorm_congr_enorm_ae (Filter.Eventually.of_forall fun x => by
      rw [eK, enorm_eq_self])).symm
  have hng : lqNorm p g = eLpNorm g' (ENNReal.ofReal p) volume := by
    rw [sky_lqNorm_eq_eLpNorm hp]
    exact (eLpNorm_congr_enorm_ae (by
      filter_upwards [eg] with x hx
      rw [hx, enorm_eq_self])).symm
  rw [sky_lqNorm_eq_eLpNorm hq, hconv, hnK, hng]
  exact Conv.eLpNorm_convAbs_le_young (μ := volume) hK'm hg'm hb hp hq (by linarith)

theorem sepKdYoungScaled_proved : UnforcedLeray.Short.PartIIIb.Concrete.SepKdYoungScaled := by
  intro j p q b hp hb hq h
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hβ : 0 < (4 + (j : ℝ)) * b - 3 := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  set C0 : ℝ := (4 * Real.pi / ((4 + (j : ℝ)) * b - 3)) ^ (1 / b) with hC0
  have hC0pos : 0 < C0 := by rw [hC0]; positivity
  refine ⟨C0, hC0pos.le, ?_⟩
  intro D hD l hl0 hl1 g' hg'
  have hKb := sky_kernel_Lb j hb hD
  rw [← hC0] at hKb
  have hepos : 0 < C0 * D ^ (-4 - (j : ℝ) + 3 / b) := by positivity
  have hlpos : 0 < l ^ (-3 + 3 / p) := by positivity
  by_cases htop : lqNorm p g' = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hlpos).ne',
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr hepos).ne']
    exact le_top
  · set S := IIIa.sepKd j D with hS
    set gl : Space → ℝ≥0∞ := fun w => g' (l⁻¹ • w) with hgl
    have hglm : Measurable gl := hg'.comp (measurable_const_smul l⁻¹)
    have hdil : lqNorm p gl = ENNReal.ofReal ((l⁻¹) ^ (-3 / p)) * lqNorm p g' :=
      sky_lqNorm_dil hp0 g' (inv_pos.mpr hl0)
    have hgltop : lqNorm p gl ≠ ⊤ := by
      rw [hdil]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop
    have step1 : ∀ y : Space, ∫⁻ z, S (y - l • z) * g' z =
        ENNReal.ofReal (|l ^ 3|⁻¹) * ∫⁻ w, S (y - w) * gl w := by
      intro y
      have := sky_lintegral_comp_smul (c := l) hl0.ne' (fun w => S (y - w) * gl w)
      simp only [hgl, inv_smul_smul₀ hl0.ne'] at this
      exact this
    have hfun : (fun y => ∫⁻ z : Space, S (y - l • z) * g' z) =
        fun y => ENNReal.ofReal (|l ^ 3|⁻¹) * ∫⁻ w, S (y - w) * gl w := funext step1
    rw [hfun, sky_lqNorm_const_mul hq0 ENNReal.ofReal_ne_top]
    have hy := sky_young_conv S gl (sky_sepKd_measurable j D) (sky_sepKd_ne_top j D) hglm hb hp hq
      h hgltop
    have hid : ENNReal.ofReal (l ^ (-3 + 3 / p)) =
        ENNReal.ofReal (|l ^ 3|⁻¹) * ENNReal.ofReal ((l⁻¹) ^ (-3 / p)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [abs_of_pos (by positivity), Real.inv_rpow hl0.le, neg_div, Real.rpow_neg hl0.le,
        inv_inv, Real.rpow_add hl0, ← Real.rpow_natCast, Real.rpow_neg hl0.le]
      norm_num
    calc ENNReal.ofReal (|l ^ 3|⁻¹) * lqNorm q (fun y => ∫⁻ w, S (y - w) * gl w)
        ≤ ENNReal.ofReal (|l ^ 3|⁻¹) * (lqNorm b S * lqNorm p gl) := by gcongr
      _ = _ := by
        rw [hKb, hdil, hid]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
