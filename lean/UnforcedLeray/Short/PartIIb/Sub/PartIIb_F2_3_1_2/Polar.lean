import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_2.Dil

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.PlanarModesHelp

open UnforcedLeray.Short.IIb

/-- The Euclidean radius on the plane. -/
def rho (x : B0579.Plane) : ℝ := Real.sqrt (x.1 ^ 2 + x.2 ^ 2)

lemma measurable_rho : Measurable rho := by unfold rho; fun_prop

lemma rho_polar (p : ℝ × ℝ) (hp : 0 < p.1) : rho (polarCoord.symm p) = p.1 := by
  unfold rho
  rw [polarCoord_symm_apply]
  have : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq p.2]
  simp only
  rw [this, Real.sqrt_sq hp.le]

lemma lint_radial (F : ℝ → ℝ≥0∞) (hF : AEMeasurable F (volume.restrict (Ioi (0 : ℝ)))) :
    ∫⁻ x : B0579.Plane, F (rho x) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * F r := by
  rw [← lintegral_comp_polarCoord_symm]
  have h1 : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • F (rho (polarCoord.symm p)) =
      ∫⁻ p in polarCoord.target, (ENNReal.ofReal p.1 * F p.1) * 1 := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun p hp => ?_)
    rw [rho_polar p hp.1, smul_eq_mul, mul_one]
  rw [h1, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hm : AEMeasurable (fun r => ENNReal.ofReal r * F r) (volume.restrict (Ioi (0 : ℝ))) :=
    (ENNReal.measurable_ofReal.aemeasurable).mul hF
  rw [lintegral_prod_mul hm aemeasurable_const]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
  rw [mul_comm]
  congr 1
  simp [two_mul, sub_neg_eq_add]

lemma rho_preimage_null (N : Set ℝ) (hN : volume (N ∩ Ioi 0) = 0) : volume (rho ⁻¹' N) = 0 := by
  set T := toMeasurable volume (N ∩ Ioi 0) with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hT0 : volume T = 0 := by rw [hT, measure_toMeasurable]; exact hN
  have hsub : rho ⁻¹' N ⊆ {0} ∪ rho ⁻¹' T := by
    intro x hx
    by_cases h0 : x = 0
    · left; exact h0
    · right
      have : 0 < rho x := by
        unfold rho
        apply Real.sqrt_pos.2
        by_contra hle
        apply h0
        have h1 : x.1 ^ 2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
        have h2 : x.2 ^ 2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
        exact Prod.ext (pow_eq_zero_iff (by norm_num) |>.1 h1) (pow_eq_zero_iff (by norm_num) |>.1 h2)
      exact subset_toMeasurable _ _ ⟨hx, this⟩
  have hρT : volume (rho ⁻¹' T) = 0 := by
    have h := lint_radial (T.indicator 1) (measurable_one.indicator hTm).aemeasurable
    have e : (fun x => T.indicator (1 : ℝ → ℝ≥0∞) (rho x)) = (rho ⁻¹' T).indicator 1 := by
      funext x; rfl
    rw [e, lintegral_indicator_one (measurable_rho hTm)] at h
    rw [h]
    have : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * T.indicator (1 : ℝ → ℝ≥0∞) r = 0 := by
      rw [lintegral_eq_zero_iff' ?_]
      · have : ∀ᵐ r : ℝ, r ∉ T := measure_eq_zero_iff_ae_notMem.1 hT0
        filter_upwards [ae_restrict_of_ae this] with r hr
        simp [hr]
      · exact ((ENNReal.measurable_ofReal.mul (measurable_one.indicator hTm))).aemeasurable.restrict
    rw [this, mul_zero]
  refine measure_mono_null hsub (measure_union_null (by simp) hρT)

end UnforcedLeray.Short.IIb.PlanarModesHelp
