import UnforcedLeray.Short.PartI.Sub.C09

/-!
# Part I, task `PartI:C09`, target `planarGreenL2`: the Green term is `L²` (source line 1140)

Proves `PlanarGreenL2` (`Short/PartI/Sub/C09.lean`): for `f ∈ X_G`, the planar function
`u = Rf(r) e^{2iϑ}` and `planar f` lie in `L²(ℝ²)`, with `‖u‖₂² ≤ C‖f‖²` and `‖planar f‖₂² ≤ C‖f‖²`.

* Part A (`planar f`): `B0122.integral_sq_le_gauss` with `gaussNormSq (planar f) = 2π‖f‖²`
  (`B0121.gaussNormSq_angularTwoField`) and `sqrtConst² = (4π)⁻¹`, so the constant is `1/2`.
* Part B (`u`): the unweighted polar identity `∫‖u‖² = 2π ∫_{(0,∞)} ‖Rf(r)‖² r dr`
  (`integral_comp_polarCoord_symm`), the pointwise bound `|Rf(r)| ≤ C‖f‖ min(r, r⁻²)`
  (`B0086.green_bound_XG`), and `∫_{(0,∞)} min(r, r⁻²)² r dr < ∞` (split at `1`).
  Integrability on `ℝ²` uses the lintegral polar change of variables.

The constant is `C = 1/2 + 2π C_R² I`, where `C_R` is the constant of `green_bound_XG` and
`I = ∫_{(0,∞)} min(r, r⁻²)² r dr`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal Real

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-! ## The radial majorant `min(r, r⁻²)² r` -/

/-- `∫_{(0,∞)} min(r, r⁻²)² r dr` is finite: `r³` on `(0,1]`, `r⁻³` on `(1,∞)`. -/
theorem planarGreenL2_min_integrable :
    IntegrableOn (fun r : ℝ => (min r (r ^ 2)⁻¹) ^ 2 * r) (Ioi (0 : ℝ)) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  refine IntegrableOn.union ?_ ?_
  · have h3 : IntegrableOn (fun r : ℝ => r ^ 3) (Ioc (0 : ℝ) 1) :=
      (continuous_pow 3).integrableOn_Ioc
    refine h3.congr_fun (fun r hr => ?_) measurableSet_Ioc
    show r ^ 3 = (min r (r ^ 2)⁻¹) ^ 2 * r
    have hr0 : 0 < r := hr.1
    have hr1 : r ≤ 1 := hr.2
    have hmin : min r (r ^ 2)⁻¹ = r := by
      apply min_eq_left
      rw [inv_eq_one_div, le_div_iff₀ (pow_pos hr0 2)]
      calc r * r ^ 2 = r ^ 3 := by ring
        _ ≤ 1 := pow_le_one₀ hr0.le hr1
    rw [hmin]
    ring
  · have h3 : IntegrableOn (fun r : ℝ => r ^ (-3 : ℝ)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    refine h3.congr_fun (fun r hr => ?_) measurableSet_Ioi
    show r ^ (-3 : ℝ) = (min r (r ^ 2)⁻¹) ^ 2 * r
    have hr1 : 1 < r := hr
    have hr0 : 0 < r := by linarith
    have hmin : min r (r ^ 2)⁻¹ = (r ^ 2)⁻¹ := by
      apply min_eq_right
      exact (inv_le_one_of_one_le₀ (by nlinarith)).trans hr1.le
    rw [hmin, show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hr0.le,
      Real.rpow_natCast]
    field_simp

/-! ## Unweighted polar identity -/

/-- The unweighted polar identity for the planar function of a radial profile. It needs no
integrability: both sides are the same integral in two coordinate systems. -/
theorem planarGreenL2_polar_integral (g : ℝ → ℂ) :
    ∫ z : ℝ × ℝ, ‖UnforcedLeray.B0010.angularTwoField g z‖ ^ 2 =
      2 * π * ∫ r in Ioi (0 : ℝ), ‖g r‖ ^ 2 * r := by
  rw [← integral_comp_polarCoord_symm]
  have key : ∀ p ∈ polarCoord.target,
      p.1 • ‖UnforcedLeray.B0010.angularTwoField g (polarCoord.symm p)‖ ^ 2 =
        (‖g p.1‖ ^ 2 * p.1) * (fun _ : ℝ => (1 : ℝ)) p.2 := by
    intro p hp
    rw [polarCoord_target] at hp
    have hF : UnforcedLeray.B0010.angularTwoField g (polarCoord.symm p) =
        g p.1 * Complex.exp (2 * Complex.I * (p.2 : ℂ)) := by
      rw [polarCoord_symm_apply]
      exact UnforcedLeray.B0010.angularTwoField_polar g (Set.mem_Ioi.1 hp.1) p.2
    rw [hF, norm_mul, UnforcedLeray.B0121.norm_exp_two_mul_I]
    simp only [smul_eq_mul, mul_one]
    ring
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet key, polarCoord_target,
    Measure.volume_eq_prod,
    setIntegral_prod_mul (μ := volume) (ν := volume) (fun r => ‖g r‖ ^ 2 * r)
      (fun _ : ℝ => (1 : ℝ)) (Ioi 0) (Ioo (-π) π)]
  have hI : ∫ _ in Ioo (-π) π, (1 : ℝ) = 2 * π := by
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  rw [hI]
  ring

/-! ## Measurability and integrability on `ℝ²` -/

/-- The planar function of a radial profile continuous on `(0, ∞)` is a.e. strongly measurable. -/
theorem planarGreenL2_aesm (g : ℝ → ℂ) (hc : ContinuousOn g (Ioi (0 : ℝ))) :
    AEStronglyMeasurable (UnforcedLeray.B0010.angularTwoField g) volume := by
  have hr : Continuous fun z : ℝ × ℝ => (polarCoord z).1 := by
    show Continuous fun z : ℝ × ℝ => Real.sqrt (z.1 ^ 2 + z.2 ^ 2)
    fun_prop
  have hcont : ContinuousOn (fun z : ℝ × ℝ => g (polarCoord z).1) ({0}ᶜ : Set (ℝ × ℝ)) :=
    hc.comp hr.continuousOn fun z hz => UnforcedLeray.B0122.polarRadius_pos hz
  have hae1 : AEStronglyMeasurable (fun z : ℝ × ℝ => g (polarCoord z).1) volume := by
    have h := hcont.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : ℝ × ℝ)).compl
    have hfull : volume.restrict ({0}ᶜ : Set (ℝ × ℝ)) = volume :=
      Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.2 (measure_singleton 0))
    rwa [hfull] at h
  have hae2 : AEStronglyMeasurable
      (fun z : ℝ × ℝ => Complex.exp (2 * Complex.I * ((polarCoord z).2 : ℂ))) volume :=
    ((Complex.measurable_ofReal.comp
      UnforcedLeray.B0121.measurable_polarCoord_fun.snd).const_mul (2 * Complex.I)).cexp.aestronglyMeasurable
  exact hae1.mul hae2

/-- The planar function of a radial profile is in `L²(ℝ²)` once `∫_{(0,∞)} ‖g r‖² r dr < ∞`. -/
theorem planarGreenL2_integrable_sq (g : ℝ → ℂ) (hc : ContinuousOn g (Ioi (0 : ℝ)))
    (hi : IntegrableOn (fun r : ℝ => ‖g r‖ ^ 2 * r) (Ioi (0 : ℝ))) :
    Integrable (fun z : ℝ × ℝ => ‖UnforcedLeray.B0010.angularTwoField g z‖ ^ 2) := by
  refine ⟨((planarGreenL2_aesm g hc).norm.aemeasurable.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => by positivity)]
  rw [← lintegral_comp_polarCoord_symm]
  have hm : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ))) :=
    hc.aestronglyMeasurable measurableSet_Ioi
  have hφm : AEMeasurable (fun r : ℝ => ENNReal.ofReal (‖g r‖ ^ 2 * r))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hm.norm.aemeasurable.pow_const 2).mul measurable_id.aemeasurable)
  calc ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 •
          ENNReal.ofReal (‖UnforcedLeray.B0010.angularTwoField g (polarCoord.symm p)‖ ^ 2)
      = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
          (fun r : ℝ => ENNReal.ofReal (‖g r‖ ^ 2 * r)) p.1 *
            (fun _ : ℝ => (1 : ℝ≥0∞)) p.2 := by
        rw [polarCoord_target]
        refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p hp => ?_)
        have hr : 0 < p.1 := hp.1
        have hFp : UnforcedLeray.B0010.angularTwoField g (polarCoord.symm p) =
            g p.1 * Complex.exp (2 * Complex.I * (p.2 : ℂ)) := by
          rw [polarCoord_symm_apply]
          exact UnforcedLeray.B0010.angularTwoField_polar g hr p.2
        have hn : ‖UnforcedLeray.B0010.angularTwoField g (polarCoord.symm p)‖ ^ 2 =
            ‖g p.1‖ ^ 2 := by
          rw [hFp, norm_mul, UnforcedLeray.B0121.norm_exp_two_mul_I, mul_one]
        rw [hn, smul_eq_mul, ← ENNReal.ofReal_mul hr.le]
        simp only [mul_one]
        congr 1
        ring
    _ = (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (‖g r‖ ^ 2 * r)) *
          ∫⁻ _ in Ioo (-π) π, (1 : ℝ≥0∞) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact lintegral_prod_mul hφm aemeasurable_const
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (Integrable.lintegral_lt_top hi) ?_
        rw [lintegral_one, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
        exact ENNReal.ofReal_lt_top

/-! ## The radial bound -/

/-- A radial profile with the pointwise bound `‖g r‖ ≤ K min(r, r⁻²)` satisfies
`∫_{(0,∞)} ‖g r‖² r dr ≤ K² I`, where `I = ∫_{(0,∞)} min(r, r⁻²)² r dr`, and is integrable. -/
theorem planarGreenL2_radial (g : ℝ → ℂ) (K : ℝ) (hc : ContinuousOn g (Ioi (0 : ℝ)))
    (hg : ∀ r : ℝ, 0 < r → ‖g r‖ ≤ K * min r (r ^ 2)⁻¹) :
    IntegrableOn (fun r : ℝ => ‖g r‖ ^ 2 * r) (Ioi (0 : ℝ)) ∧
      ∫ r in Ioi (0 : ℝ), ‖g r‖ ^ 2 * r ≤
        K ^ 2 * ∫ r in Ioi (0 : ℝ), (min r (r ^ 2)⁻¹) ^ 2 * r := by
  have hm : AEStronglyMeasurable (fun r : ℝ => ‖g r‖ ^ 2 * r)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((hc.aestronglyMeasurable measurableSet_Ioi).norm.aemeasurable.pow_const 2 |>.mul
      measurable_id.aemeasurable).aestronglyMeasurable
  have hnn : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ ‖g r‖ ^ 2 * r :=
    (ae_restrict_mem measurableSet_Ioi).mono fun r hr =>
      mul_nonneg (sq_nonneg _) (Set.mem_Ioi.1 hr).le
  have hle : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖g r‖ ^ 2 * r ≤ K ^ 2 * ((min r (r ^ 2)⁻¹) ^ 2 * r) :=
    (ae_restrict_mem measurableSet_Ioi).mono fun r hr => by
      have hr0 : 0 < r := hr
      have h1 : ‖g r‖ ^ 2 ≤ (K * min r (r ^ 2)⁻¹) ^ 2 := by
        have := hg r hr0
        nlinarith [norm_nonneg (g r)]
      calc ‖g r‖ ^ 2 * r ≤ (K * min r (r ^ 2)⁻¹) ^ 2 * r :=
            mul_le_mul_of_nonneg_right h1 hr0.le
        _ = K ^ 2 * ((min r (r ^ 2)⁻¹) ^ 2 * r) := by ring
  have hint : IntegrableOn (fun r : ℝ => K ^ 2 * ((min r (r ^ 2)⁻¹) ^ 2 * r))
      (Ioi (0 : ℝ)) :=
    Integrable.const_mul planarGreenL2_min_integrable (K ^ 2)
  have hI : IntegrableOn (fun r : ℝ => ‖g r‖ ^ 2 * r) (Ioi (0 : ℝ)) :=
    Integrable.mono' hint hm ((hnn.and hle).mono fun r hr => by
      rw [Real.norm_of_nonneg hr.1]
      exact hr.2)
  refine ⟨hI, ?_⟩
  calc ∫ r in Ioi (0 : ℝ), ‖g r‖ ^ 2 * r
      ≤ ∫ r in Ioi (0 : ℝ), K ^ 2 * ((min r (r ^ 2)⁻¹) ^ 2 * r) :=
        integral_mono_of_nonneg hnn hint hle
    _ = K ^ 2 * ∫ r in Ioi (0 : ℝ), (min r (r ^ 2)⁻¹) ^ 2 * r :=
        integral_const_mul _ _

/-! ## The target -/

/-- **`PartI:C09` target `planarGreenL2`** (source line 1140): for `f ∈ X_G`, `Rf(r)e^{2iϑ}` and
`planar f` lie in `L²(ℝ²)` with the bounds of `PlanarGreenL2`. -/
theorem planarGreenL2 : PlanarGreenL2 := by
  obtain ⟨CR, hCR0, hCR⟩ := UnforcedLeray.B0086.green_bound_XG
  have hI0 : 0 ≤ ∫ r in Ioi (0 : ℝ), (min r (r ^ 2)⁻¹) ^ 2 * r :=
    setIntegral_nonneg measurableSet_Ioi fun r hr =>
      mul_nonneg (sq_nonneg _) (Set.mem_Ioi.1 hr).le
  have hX : 0 ≤ 2 * π * CR ^ 2 * ∫ r in Ioi (0 : ℝ), (min r (r ^ 2)⁻¹) ^ 2 * r :=
    mul_nonneg (mul_nonneg (by positivity) (sq_nonneg CR)) hI0
  have hpi : π ≠ 0 := Real.pi_ne_zero
  unfold PlanarGreenL2
  refine ⟨1 / 2 + 2 * π * CR ^ 2 * ∫ r in Ioi (0 : ℝ), (min r (r ^ 2)⁻¹) ^ 2 * r,
    by linarith, fun f => ?_⟩
  have hgc : ContinuousOn (UnforcedLeray.B0011.R ⇑f) (Ioi (0 : ℝ)) :=
    UnforcedLeray.B0012.continuousOn_R f
  obtain ⟨hIR, hIRbd⟩ := planarGreenL2_radial (UnforcedLeray.B0011.R ⇑f) (CR * ‖f‖) hgc
    (fun r hr => (hCR f r hr).1)
  have hsq : UnforcedLeray.B0093.sqrtConst ^ 2 = (4 * π)⁻¹ := by
    unfold UnforcedLeray.B0093.sqrtConst
    exact Real.sq_sqrt (by positivity)
  have hg2 : UnforcedLeray.B0121.gaussNormSq (UnforcedLeray.B0121.planar f) =
      2 * π * ‖f‖ ^ 2 := by
    have h := UnforcedLeray.B0121.gaussNormSq_angularTwoField (Lp.memLp f)
    rw [Lp.toLp_coeFn] at h
    exact h
  refine ⟨(memLp_two_iff_integrable_sq_norm (planarGreenL2_aesm _ hgc)).2
      (planarGreenL2_integrable_sq _ hgc hIR),
    (UnforcedLeray.B0121.memGaussL2_planar f).memLp, ?_, ?_⟩
  · rw [planarGreenL2_polar_integral]
    calc 2 * π * ∫ r in Ioi (0 : ℝ), ‖UnforcedLeray.B0011.R ⇑f r‖ ^ 2 * r
        ≤ 2 * π * ((CR * ‖f‖) ^ 2 * ∫ r in Ioi (0 : ℝ), (min r (r ^ 2)⁻¹) ^ 2 * r) :=
          mul_le_mul_of_nonneg_left hIRbd (by positivity)
      _ = (2 * π * CR ^ 2 * ∫ r in Ioi (0 : ℝ), (min r (r ^ 2)⁻¹) ^ 2 * r) * ‖f‖ ^ 2 := by ring
      _ ≤ (1 / 2 + 2 * π * CR ^ 2 * ∫ r in Ioi (0 : ℝ), (min r (r ^ 2)⁻¹) ^ 2 * r) * ‖f‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  · calc ∫ z, ‖UnforcedLeray.B0121.planar f z‖ ^ 2
        ≤ UnforcedLeray.B0093.sqrtConst ^ 2 *
            UnforcedLeray.B0121.gaussNormSq (UnforcedLeray.B0121.planar f) :=
          UnforcedLeray.B0122.integral_sq_le_gauss (UnforcedLeray.B0121.memGaussL2_planar f)
      _ = (4 * π)⁻¹ * (2 * π * ‖f‖ ^ 2) := by rw [hsq, hg2]
      _ = 1 / 2 * ‖f‖ ^ 2 := by field_simp; ring
      _ ≤ (1 / 2 + 2 * π * CR ^ 2 * ∫ r in Ioi (0 : ℝ), (min r (r ^ 2)⁻¹) ^ 2 * r) * ‖f‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end UnforcedLeray.Short.PartI
