import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F1

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.PlanarModesHelp

open UnforcedLeray.Short.IIb

lemma density_continuous (m : ℝ) (hm : 0 ≤ m) : Continuous (fun x : B0579.Plane => B0579.density m x) := by
  unfold B0579.density
  refine Continuous.comp continuous_real_toNNReal ?_
  refine Continuous.rpow_const ?_ (fun x => Or.inr hm)
  unfold B0579.jb
  fun_prop

theorem isLocFin (m : ℝ) (hm : 0 ≤ m) : IsLocallyFiniteMeasure (planeMeasure m) := by
  unfold planeMeasure
  exact IsLocallyFiniteMeasure.withDensity_coe (density_continuous m hm)

lemma lint_planeMeasure (m : ℝ) (hm : 0 ≤ m) (φ : B0579.Plane → ℝ≥0∞) :
    ∫⁻ x, φ x ∂planeMeasure m = ∫⁻ x, (B0579.density m x : ℝ≥0∞) * φ x := by
  unfold planeMeasure
  have := lintegral_withDensity_eq_lintegral_mul_non_measurable (volume : Measure B0579.Plane)
    (f := fun x => (B0579.density m x : ℝ≥0∞))
    (measurable_coe_nnreal_ennreal.comp (density_continuous m hm).measurable)
    (Filter.Eventually.of_forall (fun x => ENNReal.coe_lt_top)) φ
  rw [this]; rfl

lemma lint_smul (s : ℝ) (hs : s ≠ 0) (Ψ : B0579.Plane → ℝ≥0∞) :
    ∫⁻ x, Ψ x = ENNReal.ofReal (s ^ 2) * ∫⁻ y, Ψ (s • y) := by
  have hmap := Measure.map_addHaar_smul (volume : Measure B0579.Plane) hs
  let e : B0579.Plane ≃ᵐ B0579.Plane := (Homeomorph.smulOfNeZero (α := B0579.Plane) s hs).toMeasurableEquiv
  have h1 : ∫⁻ y, Ψ (s • y) = ∫⁻ x, Ψ x ∂(Measure.map (fun y : B0579.Plane => s • y) volume) := by
    have := lintegral_map_equiv Ψ e (μ := (volume : Measure B0579.Plane))
    exact this.symm
  rw [h1, hmap]
  simp only [lintegral_smul_measure]
  have : Module.finrank ℝ B0579.Plane = 2 := by simp [B0579.Plane]
  rw [this, smul_eq_mul, ← mul_assoc]
  have h2 : ENNReal.ofReal (s ^ 2) * ENNReal.ofReal |(s ^ 2)⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), abs_of_nonneg (by positivity)]
    rw [mul_inv_cancel₀ (by positivity)]; simp
  rw [h2, one_mul]

/-- The dilation `x ↦ x/√a` of the plane. -/
def sc (a : ℝ) (x : B0579.Plane) : B0579.Plane := (Real.sqrt a)⁻¹ • x

lemma density_coe (m : ℝ) (x : B0579.Plane) :
    (B0579.density m x : ℝ≥0∞) = ENNReal.ofReal (B0579.jb x ^ m) := rfl

lemma density_smul_le (m a : ℝ) (hm : 0 ≤ m) (ha : 1 ≤ a) (y : B0579.Plane) :
    (B0579.density m (Real.sqrt a • y) : ℝ≥0∞) ≤
      ENNReal.ofReal (a ^ m) * (B0579.density m y : ℝ≥0∞) := by
  rw [density_coe, density_coe, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
  have hjb : B0579.jb (Real.sqrt a • y) ≤ a * B0579.jb y := by
    unfold B0579.jb
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have h1 : (Real.sqrt a * y.1) ^ 2 = a * y.1 ^ 2 := by rw [mul_pow, hsq]
    have h2 : (Real.sqrt a * y.2) ^ 2 = a * y.2 ^ 2 := by rw [mul_pow, hsq]
    rw [h1, h2]; nlinarith [sq_nonneg y.1, sq_nonneg y.2]
  calc B0579.jb (Real.sqrt a • y) ^ m ≤ (a * B0579.jb y) ^ m :=
        Real.rpow_le_rpow (B0579.jb_pos _).le hjb hm
    _ = a ^ m * B0579.jb y ^ m := Real.mul_rpow (by linarith) (B0579.jb_pos _).le

lemma lint_dil (m a : ℝ) (hm : 0 ≤ m) (ha : 1 ≤ a) (φ : B0579.Plane → ℝ≥0∞) :
    ∫⁻ x, φ (sc a x) ∂planeMeasure m ≤
      ENNReal.ofReal (a ^ (m + 1)) * ∫⁻ y, φ y ∂planeMeasure m := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
  rw [lint_planeMeasure m hm, lint_planeMeasure m hm]
  rw [lint_smul (Real.sqrt a) hs]
  simp only [sc, inv_smul_smul₀ hs]
  rw [hsq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hp : ENNReal.ofReal (a ^ (m + 1)) = ENNReal.ofReal a * ENNReal.ofReal (a ^ m) := by
    rw [← ENNReal.ofReal_mul (by linarith), Real.rpow_add (by linarith), Real.rpow_one]; ring_nf
  rw [hp]
  refine lintegral_mono (fun y => ?_)
  have h := density_smul_le m a hm ha y
  calc _ ≤ ENNReal.ofReal a * ((ENNReal.ofReal (a ^ m) * (B0579.density m y : ℝ≥0∞)) * φ y) := by
        exact mul_le_mul' le_rfl (mul_le_mul' h le_rfl)
    _ = _ := by ring


lemma measurable_sc (a : ℝ) : Measurable (sc a) := by
  unfold sc; exact measurable_const_smul _

lemma qmp_sc (m a : ℝ) (hm : 0 ≤ m) (ha : 1 ≤ a) :
    Measure.QuasiMeasurePreserving (sc a) (planeMeasure m) (planeMeasure m) := by
  refine ⟨measurable_sc a, ?_⟩
  intro N hN
  have hT := measurableSet_toMeasurable (planeMeasure m) N
  have hT0 : planeMeasure m (toMeasurable (planeMeasure m) N) = 0 := by
    rw [measure_toMeasurable]; exact hN
  refine measure_mono_null (subset_toMeasurable (planeMeasure m) N) ?_
  rw [Measure.map_apply (measurable_sc a) hT]
  have h := lint_dil m a hm ha ((toMeasurable (planeMeasure m) N).indicator 1)
  have e : (fun x => (toMeasurable (planeMeasure m) N).indicator (1 : B0579.Plane → ℝ≥0∞) (sc a x))
      = ((sc a) ⁻¹' toMeasurable (planeMeasure m) N).indicator 1 := by
    funext x; rfl
  rw [e, lintegral_indicator_one ((measurable_sc a) hT), lintegral_indicator_one hT, hT0,
    mul_zero] at h
  exact le_antisymm h bot_le


/-- Dilated function `a^{-2} h(x/√a)`. -/
def dl (a : ℝ) (h : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ := a ^ (-2 : ℝ) * h (sc a x)

lemma eLpNorm_two_eq (μ : Measure B0579.Plane) (f : B0579.Plane → ℝ) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp)]
  simp

lemma dl_sub (a : ℝ) (f g : B0579.Plane → ℝ) : dl a (f - g) = dl a f - dl a g := by
  funext x; simp [dl, mul_sub]

lemma enorm_dl_le (a : ℝ) (ha : 1 ≤ a) (h : B0579.Plane → ℝ) (x : B0579.Plane) :
    ‖dl a h x‖ₑ ≤ ‖h (sc a x)‖ₑ := by
  unfold dl
  rw [enorm_mul]
  have : ‖a ^ (-2 : ℝ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm_eq_enorm]
    simp only [ENNReal.ofReal_le_one]
    rw [Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos ha (by norm_num)
  calc _ ≤ 1 * ‖h (sc a x)‖ₑ := mul_le_mul' this le_rfl
    _ = _ := one_mul _

lemma lint_dl_le (m a A : ℝ) (hm : 0 ≤ m) (ha : 1 ≤ a) (haA : a ≤ A) (h : B0579.Plane → ℝ) :
    ∫⁻ x, ‖dl a h x‖ₑ ^ (2 : ℝ) ∂planeMeasure m ≤
      ENNReal.ofReal (A ^ (m + 1)) * ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂planeMeasure m := by
  calc _ ≤ ∫⁻ x, (fun y => ‖h y‖ₑ ^ (2 : ℝ)) (sc a x) ∂planeMeasure m :=
        lintegral_mono (fun x => ENNReal.rpow_le_rpow (enorm_dl_le a ha h x) (by norm_num))
    _ ≤ ENNReal.ofReal (a ^ (m + 1)) * ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂planeMeasure m :=
        lint_dil m a hm ha _
    _ ≤ _ := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        exact Real.rpow_le_rpow (by linarith) haA (by linarith)

lemma eLpNorm_dl_le (m a A : ℝ) (hm : 0 ≤ m) (ha : 1 ≤ a) (haA : a ≤ A) (h : B0579.Plane → ℝ) :
    eLpNorm (dl a h) 2 (planeMeasure m) ≤
      ENNReal.ofReal (A ^ (m + 1)) ^ (1 / 2 : ℝ) * eLpNorm h 2 (planeMeasure m) := by
  rw [eLpNorm_two_eq, eLpNorm_two_eq, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  exact ENNReal.rpow_le_rpow (lint_dl_le m a A hm ha haA h) (by norm_num)

lemma memLp_dl (m a A : ℝ) (hm : 0 ≤ m) (ha : 1 ≤ a) (haA : a ≤ A) {h : B0579.Plane → ℝ}
    (hh : MemLp h 2 (planeMeasure m)) : MemLp (dl a h) 2 (planeMeasure m) := by
  refine ⟨?_, ?_⟩
  · exact (hh.1.comp_quasiMeasurePreserving (qmp_sc m a hm ha)).const_mul _
  · exact lt_of_le_of_lt (eLpNorm_dl_le m a A hm ha haA h)
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) hh.2)


end UnforcedLeray.Short.IIb.PlanarModesHelp
