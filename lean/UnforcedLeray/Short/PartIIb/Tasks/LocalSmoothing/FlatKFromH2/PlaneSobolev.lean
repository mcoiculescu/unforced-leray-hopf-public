import UnforcedLeray.Short.PartIIb.Tasks.LocalSmoothing.FlatKFromH2.Strip

/-!
# `PartII-b:F8/2` helper: the periodic-strip Sobolev inequality

`plane_sobolev`: for `c ≥ 4` and `c`-periodic `u, g₁, g₂ : ℝ × ℝ → ℂ`, square integrable on the
cell, with `g₁ = ∂_q u`, `g₂ = ∂_η u` tested against the mollifiers `kern n (x - ·)` for `x` in a dense
set,
`‖u‖_{L^{11/4}(cell)} ≤ planeK (‖u‖_{L²(cell)} + ‖g₁‖_{L²(cell)} + ‖g₂‖_{L²(cell)})`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIb.FlatKH2

/-- The constant of the periodic-strip Sobolev inequality. -/
def planeK : ℝ≥0∞ :=
  ((2 * (gnsC : ℝ≥0∞)) ^ (3 / 4 : ℝ)) ^ (4 / 11 : ℝ) *
    ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (1 + 2 * ENNReal.ofReal (4 * stM)))

theorem planeK_ne_top : planeK ≠ ⊤ := by
  unfold planeK
  apply ENNReal.mul_ne_top
  · apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
  · apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num)
    · exact ENNReal.add_ne_top.2 ⟨by norm_num, ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩

/-- **Periodic-strip Sobolev inequality** `H¹ ⊂ L^{11/4}`. -/
theorem plane_sobolev {c : ℝ} (hc : 4 ≤ c) {u g₁ g₂ : ℝ × ℝ → ℂ}
    (hu : AEStronglyMeasurable u volume) (hg₁ : AEStronglyMeasurable g₁ volume)
    (hg₂ : AEStronglyMeasurable g₂ volume)
    (hpu : APer c u) (hp₁ : APer c g₁) (hp₂ : APer c g₂)
    (hfu : eLpNorm u 2 (volume.restrict (strip (-(c / 2)) (c / 2))) < ⊤)
    (hf₁ : eLpNorm g₁ 2 (volume.restrict (strip (-(c / 2)) (c / 2))) < ⊤)
    (hf₂ : eLpNorm g₂ 2 (volume.restrict (strip (-(c / 2)) (c / 2))) < ⊤)
    {D : Set (ℝ × ℝ)} (hD : Dense D)
    (hid₁ : ∀ n : ℕ, ∀ x ∈ D, ∫ y, (kern n (x - y) : ℂ) * g₁ y =
      ∫ y, ((fderiv ℝ (kern n) (x - y) (1, 0) : ℝ) : ℂ) * u y)
    (hid₂ : ∀ n : ℕ, ∀ x ∈ D, ∫ y, (kern n (x - y) : ℂ) * g₂ y =
      ∫ y, ((fderiv ℝ (kern n) (x - y) (0, 1) : ℝ) : ℂ) * u y) :
    eLpNorm u (ENNReal.ofReal (11 / 4)) (volume.restrict (strip (-(c / 2)) (c / 2))) ≤
      planeK * (eLpNorm u 2 (volume.restrict (strip (-(c / 2)) (c / 2))) +
        eLpNorm g₁ 2 (volume.restrict (strip (-(c / 2)) (c / 2))) +
        eLpNorm g₂ 2 (volume.restrict (strip (-(c / 2)) (c / 2)))) := by
  have hc0 : 0 < c := by linarith
  set S := strip (-(c / 2)) (c / 2) with hS
  set Bu := eLpNorm u 2 (volume.restrict S) with hBu
  set B₁ := eLpNorm g₁ 2 (volume.restrict S) with hB₁
  set B₂ := eLpNorm g₂ 2 (volume.restrict S) with hB₂
  set s3 : ℝ≥0∞ := (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) with hs3
  set m4 : ℝ≥0∞ := ENNReal.ofReal (4 * stM) with hm4
  have hs3top : s3 ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num)
  have hlu := locallyIntegrable_of_aper hc0 hu hpu hfu
  have hl₁ := locallyIntegrable_of_aper hc0 hg₁ hp₁ hf₁
  have hl₂ := locallyIntegrable_of_aper hc0 hg₂ hp₂ hf₂
  have hd₁ : ∀ (n : ℕ) (x : ℝ × ℝ),
      fderiv ℝ (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x (1, 0) =
        (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g₁) x :=
    fun n x => ident_ext n hlu hl₁ hD (1, 0) (hid₁ n) x
  have hd₂ : ∀ (n : ℕ) (x : ℝ × ℝ),
      fderiv ℝ (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x (0, 1) =
        (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g₂) x :=
    fun n x => ident_ext n hlu hl₂ hD (0, 1) (hid₂ n) x
  -- three-cell `L²` bounds
  have h3 : ∀ h : ℝ × ℝ → ℂ, AEStronglyMeasurable h volume → APer c h →
      eLpNorm h 2 (volume.restrict S) < ⊤ →
      LocallyIntegrable ((strip3 c).indicator h) volume ∧
        eLpNorm ((strip3 c).indicator h) 2 volume ≤ s3 * eLpNorm h 2 (volume.restrict S) := by
    intro h hm hp hfin
    have hle := eLpNorm_indicator_strip3_le hc0 hp
    refine ⟨MemLp.locallyIntegrable ⟨hm.indicator (measurableSet_strip _ _), hle.trans_lt
      (ENNReal.mul_lt_top hs3top.lt_top hfin)⟩ (by norm_num), hle⟩
  obtain ⟨hliu, h3u⟩ := h3 u hu hpu hfu
  obtain ⟨hli₁, h31⟩ := h3 g₁ hg₁ hp₁ hf₁
  obtain ⟨hli₂, h32⟩ := h3 g₂ hg₂ hp₂ hf₂
  -- the mollified indicator functions
  have hMcont : ∀ (n : ℕ) (h : ℝ × ℝ → ℂ), LocallyIntegrable h volume →
      Continuous (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) := fun n h hh =>
    (kern_hasCompactSupport n).continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (kern_contDiff n).continuous hh
  have hMl2 : ∀ (n : ℕ) (h : ℝ × ℝ → ℂ), AEStronglyMeasurable h volume →
      eLpNorm (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (strip3 c).indicator h) 2 volume ≤
        eLpNorm ((strip3 c).indicator h) 2 volume := fun n h hm =>
    conv_eLpNorm_le n (hm.indicator (measurableSet_strip _ _))
  -- the approximating sequence
  set U : ℕ → ℝ × ℝ → ℂ := fun n y =>
    cut2 (c / 2) n y • (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) y with hU
  have hMsm : ∀ n : ℕ, ContDiff ℝ 1 (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) :=
    fun n => (kern_hasCompactSupport n).contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (kern_contDiff1 n) hlu
  have hcut1 : ∀ n : ℕ, ContDiff ℝ 1 (cut2 (c / 2) n) := fun n => by
    simpa using contDiff_infty.1 (contDiff_cut2 (c / 2) n) 1
  have hUcd : ∀ n, ContDiff ℝ 1 (U n) := fun n => (hcut1 n).smul (hMsm n)
  have hUcs : ∀ n, HasCompactSupport (U n) := fun n =>
    (hasCompactSupport_cut2 (c / 2) n).smul_right
  have hUpt : ∀ (n : ℕ) (y : ℝ × ℝ), ‖U n y‖ ≤
      ‖(kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (strip3 c).indicator u) y‖ := by
    intro n y
    by_cases hy : |y.1| ≤ c / 2 + 1
    · simp only [hU]
      rw [norm_smul, conv_eq_conv_indicator hc n u hy, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_cut2_le_one _ _ _)
    · simp only [hU]
      rw [cut2_eq_zero (le_of_lt (not_le.mp hy)), zero_smul, norm_zero]
      exact norm_nonneg _
  have hU2 : ∀ n, eLpNorm (U n) 2 volume ≤ s3 * Bu := fun n =>
    ((eLpNorm_mono (fun y => hUpt n y)).trans (hMl2 n u hu)).trans h3u
  -- derivative bounds
  have hUd : ∀ (n : ℕ) (e : ℝ × ℝ) (g : ℝ × ℝ → ℂ), ‖e‖ ≤ 1 →
      (∀ x, fderiv ℝ (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x e =
        (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) →
      ∀ y, ‖fderiv ℝ (U n) y e‖ ≤
        ‖(kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (strip3 c).indicator g) y‖ +
          4 * stM * ‖(kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (strip3 c).indicator u) y‖ := by
    intro n e g he hde y
    have hM0 := stM_nonneg
    by_cases hy : |y.1| ≤ c / 2 + 1
    · have hζ : HasFDerivAt (cut2 (c / 2) n) (fderiv ℝ (cut2 (c / 2) n) y) y :=
        ((hcut1 n).differentiable (by norm_num) y).hasFDerivAt
      have hM : HasFDerivAt (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)
          (fderiv ℝ (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) y) y :=
        ((hMsm n).differentiable (by norm_num) y).hasFDerivAt
      have hUf : HasFDerivAt (U n)
          (cut2 (c / 2) n y • fderiv ℝ (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) y +
            (fderiv ℝ (cut2 (c / 2) n) y).smulRight
              ((kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) y)) y := hζ.smul hM
      rw [hUf.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [hde y, conv_eq_conv_indicator hc n g hy, conv_eq_conv_indicator hc n u hy]
      calc ‖cut2 (c / 2) n y • (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (strip3 c).indicator g) y +
            fderiv ℝ (cut2 (c / 2) n) y e • (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (strip3 c).indicator u) y‖
          ≤ ‖cut2 (c / 2) n y • (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (strip3 c).indicator g) y‖ +
            ‖fderiv ℝ (cut2 (c / 2) n) y e • (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (strip3 c).indicator u) y‖ := norm_add_le _ _
        _ ≤ 1 * ‖(kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (strip3 c).indicator g) y‖ +
            4 * stM *
              ‖(kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (strip3 c).indicator u) y‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
            gcongr
            · exact abs_cut2_le_one _ _ _
            · exact abs_fderiv_cut2_apply_le _ _ _ _ he
        _ = _ := by rw [one_mul]
    · have hopen : IsOpen {z : ℝ × ℝ | c / 2 + 1 < |z.1|} :=
        isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
      have hev : U n =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hopen.mem_nhds (not_le.mp hy)] with z hz
        simp only [hU]
        rw [cut2_eq_zero (le_of_lt hz), zero_smul]
      rw [hev.fderiv_eq, fderiv_const_apply, ContinuousLinearMap.zero_apply, norm_zero]
      positivity
  have hUd2 : ∀ (n : ℕ) (e : ℝ × ℝ) (g : ℝ × ℝ → ℂ), ‖e‖ ≤ 1 →
      AEStronglyMeasurable g volume → LocallyIntegrable ((strip3 c).indicator g) volume →
      eLpNorm ((strip3 c).indicator g) 2 volume ≤ s3 * eLpNorm g 2 (volume.restrict S) →
      (∀ x, fderiv ℝ (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x e =
        (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) →
      eLpNorm (fun y => fderiv ℝ (U n) y e) 2 volume ≤
        s3 * eLpNorm g 2 (volume.restrict S) + m4 * (s3 * Bu) := by
    intro n e g he hgm hgli hg3 hde
    have hcg := hMcont n _ hgli
    have hcu := hMcont n _ hliu
    calc eLpNorm (fun y => fderiv ℝ (U n) y e) 2 volume
        ≤ eLpNorm (fun y =>
            ‖(kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (strip3 c).indicator g) y‖ +
            4 * stM * ‖(kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (strip3 c).indicator u) y‖) 2 volume :=
          eLpNorm_mono_real (hUd n e g he hde)
      _ ≤ eLpNorm (fun y =>
            ‖(kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (strip3 c).indicator g) y‖) 2 volume +
          eLpNorm (fun y => 4 * stM * ‖(kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (strip3 c).indicator u) y‖) 2 volume :=
          eLpNorm_add_le hcg.norm.aestronglyMeasurable
            (hcu.norm.aestronglyMeasurable.const_mul _) (by norm_num)
      _ = eLpNorm ((kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (strip3 c).indicator g))
            2 volume +
          m4 * eLpNorm ((kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (strip3 c).indicator u))
            2 volume := by
          rw [eLpNorm_norm]
          congr 1
          rw [show (fun y => 4 * stM * ‖(kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (strip3 c).indicator u) y‖) = (4 * stM) • (fun y => ‖(kern n ⋆[ContinuousLinearMap.lsmul
                ℝ ℝ, volume] (strip3 c).indicator u) y‖) from rfl, eLpNorm_const_smul, eLpNorm_norm,
            Real.enorm_eq_ofReal (by positivity [stM_nonneg])]
      _ ≤ s3 * eLpNorm g 2 (volume.restrict S) + m4 * (s3 * Bu) := by
          gcongr
          · exact (hMl2 n g hgm).trans hg3
          · exact (hMl2 n u hu).trans h3u
  have hn10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp
  have hn01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp
  -- the uniform bound
  set X : ℝ≥0∞ := s3 * (1 + 2 * m4) * (Bu + B₁ + B₂) with hX
  have hbound : ∀ n, ∫⁻ y, ‖U n y‖ₑ ^ (11 / 4 : ℝ) ≤
      (2 * (gnsC : ℝ≥0∞)) ^ (3 / 4 : ℝ) * X ^ (11 / 4 : ℝ) := by
    intro n
    refine (smooth_lintegral_le (hUcd n) (hUcs n)).trans ?_
    gcongr
    calc eLpNorm (U n) 2 volume + (eLpNorm (fun y => fderiv ℝ (U n) y (1, 0)) 2 volume +
          eLpNorm (fun y => fderiv ℝ (U n) y (0, 1)) 2 volume)
        ≤ s3 * Bu + ((s3 * B₁ + m4 * (s3 * Bu)) + (s3 * B₂ + m4 * (s3 * Bu))) := by
          gcongr
          · exact hU2 n
          · exact hUd2 n (1, 0) g₁ hn10 hg₁ hli₁ h31 (hd₁ n)
          · exact hUd2 n (0, 1) g₂ hn01 hg₂ hli₂ h32 (hd₂ n)
      _ = s3 * ((1 + 2 * m4) * Bu + B₁ + B₂) := by ring
      _ ≤ s3 * ((1 + 2 * m4) * Bu + (1 + 2 * m4) * B₁ + (1 + 2 * m4) * B₂) := by
          gcongr
          · exact le_mul_of_one_le_left bot_le le_self_add
          · exact le_mul_of_one_le_left bot_le le_self_add
      _ = X := by rw [hX]; ring
  -- almost everywhere convergence
  have hconvM := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure (ℝ × ℝ))) bump_rOut_tendsto (Eventually.of_forall bump_shape) hlu
  have hconv : ∀ᵐ y : ℝ × ℝ, Tendsto (fun n => U n y) atTop
      (𝓝 (plateau (c / 2) y.1 • u y)) := by
    filter_upwards [hconvM] with y hy
    have hcut : Tendsto (fun n : ℕ => cut2 (c / 2) n y) atTop (𝓝 (plateau (c / 2) y.1)) := by
      refine tendsto_const_nhds.congr' ?_
      refine Filter.eventually_atTop.2 ⟨⌈|y.2|⌉₊, fun n hn => ?_⟩
      have h1 : |y.2| ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      simp only [cut2]
      rw [plateau_eq_one h1, mul_one]
    exact hcut.smul hy
  -- Fatou
  have hfatou : ∫⁻ y, ‖plateau (c / 2) y.1 • u y‖ₑ ^ (11 / 4 : ℝ) ≤
      (2 * (gnsC : ℝ≥0∞)) ^ (3 / 4 : ℝ) * X ^ (11 / 4 : ℝ) := by
    calc ∫⁻ y, ‖plateau (c / 2) y.1 • u y‖ₑ ^ (11 / 4 : ℝ)
        = ∫⁻ y, liminf (fun n => ‖U n y‖ₑ ^ (11 / 4 : ℝ)) atTop := by
          apply lintegral_congr_ae
          filter_upwards [hconv] with y hy
          exact (((ENNReal.continuous_rpow_const).tendsto _).comp hy.enorm).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ y, ‖U n y‖ₑ ^ (11 / 4 : ℝ)) atTop :=
          lintegral_liminf_le' (fun n =>
            ((hUcd n).continuous.enorm.measurable.pow_const _).aemeasurable)
      _ ≤ _ := liminf_le_of_frequently_le (Eventually.of_forall hbound).frequently
  -- restriction to the cell
  have hcell : ∫⁻ y in S, ‖u y‖ₑ ^ (11 / 4 : ℝ) ≤
      (2 * (gnsC : ℝ≥0∞)) ^ (3 / 4 : ℝ) * X ^ (11 / 4 : ℝ) := by
    calc ∫⁻ y in S, ‖u y‖ₑ ^ (11 / 4 : ℝ)
        = ∫⁻ y in S, ‖plateau (c / 2) y.1 • u y‖ₑ ^ (11 / 4 : ℝ) := by
          refine setLIntegral_congr_fun (measurableSet_strip _ _) (fun y hy => ?_)
          simp only [hS, strip, mem_prod, mem_Ico] at hy
          rw [plateau_eq_one (abs_le.2 ⟨hy.1.1, hy.1.2.le⟩), one_smul]
      _ ≤ ∫⁻ y, ‖plateau (c / 2) y.1 • u y‖ₑ ^ (11 / 4 : ℝ) := setLIntegral_le_lintegral _ _
      _ ≤ _ := hfatou
  have hp0 : ENNReal.ofReal (11 / 4 : ℝ) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by norm_num)]
  calc (∫⁻ y in S, ‖u y‖ₑ ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ))
      ≤ ((2 * (gnsC : ℝ≥0∞)) ^ (3 / 4 : ℝ) * X ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ)) :=
        ENNReal.rpow_le_rpow hcell (by norm_num)
    _ = ((2 * (gnsC : ℝ≥0∞)) ^ (3 / 4 : ℝ)) ^ (4 / 11 : ℝ) * X := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul X]
        norm_num
    _ = planeK * (Bu + B₁ + B₂) := by
        rw [hX, planeK]
        ring

end UnforcedLeray.Short.IIb.FlatKH2
