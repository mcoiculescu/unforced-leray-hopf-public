import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_1_aux

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Pointwise Hölder constant: `|Σ aᵢ gᵢ| ≤ 2 ‖a‖ ‖g‖_sup`. -/
theorem dualF_pt_bound (a : CMerid) (g : Fin 2 → ℝ) :
    ‖∑ i : Fin 2, a i * ((g i : ℝ) : ℂ)‖ₑ ≤ 2 * (‖a‖ₑ * ‖g‖ₑ) := by
  have h1 : ‖∑ i : Fin 2, a i * ((g i : ℝ) : ℂ)‖ ≤ 2 * (‖a‖ * ‖g‖) := by
    calc ‖∑ i : Fin 2, a i * ((g i : ℝ) : ℂ)‖ ≤ ∑ i : Fin 2, ‖a i * ((g i : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i : Fin 2, ‖a‖ * ‖g‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, Complex.norm_real]
          exact mul_le_mul (PiLp.norm_apply_le a i) (norm_le_pi_norm g i) (norm_nonneg _)
            (norm_nonneg _)
      _ = 2 * (‖a‖ * ‖g‖) := by simp
  have h2 := ENNReal.ofReal_le_ofReal h1
  rw [ofReal_norm_eq_enorm] at h2
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm,
    ofReal_norm_eq_enorm] at h2
  simpa using h2

/-- Leaf `T11/2/1/2`: cell Hölder for a.e. `σ ∈ (0,s)`. -/
theorem DualFPointwise_proof : UnforcedLeray.Short.IIb.DualFPointwise := by
  intro c r ν μ b H s hc hν hr hs hb hfl hH
  have : SFinite (Cyl.avgμ c) := sfinite_avgμ c
  have hslice := ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioi_self : Ioo (0 : ℝ) s ⊆ Ioi 0) (slice_aestronglyMeasurable hc hb)
  filter_upwards [hslice, ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) s))]
    with σ hσ hσm
  have hσ0 : 0 < σ := hσm.1
  have hσs : σ < s := hσm.2
  set g : ℝ × ℝ → (Fin 2 → ℝ) := fun p => perpGrad (fun z => H (s - σ, z)) p with hgdef
  have hgc : Continuous g := by
    refine continuous_pi fun i => ?_
    have h1 := perpGradH_continuousOn hH.smooth s i
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (σ, p)) univ :=
      (by fun_prop : Continuous fun p : ℝ × ℝ => (σ, p)).continuousOn
    have h3 := h1.comp h2 (fun p _ => (show (σ, p).1 < s from hσs))
    exact continuousOn_univ.1 h3
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hq : 0 < r / (r - 1) := div_pos (by linarith) (by linarith)
  have hq0 : ENNReal.ofReal (r / (r - 1)) ≠ 0 := (ENNReal.ofReal_pos.2 hq).ne'
  have hqt : ENNReal.ofReal (r / (r - 1)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpq : r.HolderConjugate (r / (r - 1)) := Real.HolderConjugate.conjExponent hr
  have hAeq : dfA c r b σ = (∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) := by
    unfold dfA
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ r)]
  have hBeq : dfB c (r / (r - 1)) H (s - σ) =
      (∫⁻ p, ‖g p‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^ (1 / (r / (r - 1))) := by
    unfold dfB
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt, ENNReal.toReal_ofReal hq.le]
  have hnorm : ‖(((σ : ℝ) : ℂ)) ^ μ‖ₑ = ENNReal.ofReal (σ ^ μ.re) := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_cpow_eq_rpow_re_of_pos hσ0]
  unfold dualF
  rw [enorm_mul, hnorm]
  have hint : ‖∫ p, ∑ i : Fin 2, b (σ, p) i * ((perpGrad (fun z => H (s - σ, z)) p i : ℝ) : ℂ)
      ∂(Cyl.avgμ c)‖ₑ ≤ 2 * (dfA c r b σ * dfB c (r / (r - 1)) H (s - σ)) := by
    calc _ ≤ ∫⁻ p, ‖∑ i : Fin 2, b (σ, p) i *
          ((perpGrad (fun z => H (s - σ, z)) p i : ℝ) : ℂ)‖ₑ ∂(Cyl.avgμ c) :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ p, 2 * (‖b (σ, p)‖ₑ * ‖g p‖ₑ) ∂(Cyl.avgμ c) :=
          lintegral_mono fun p => dualF_pt_bound (b (σ, p)) (g p)
      _ = 2 * ∫⁻ p, (‖b (σ, p)‖ₑ * ‖g p‖ₑ) ∂(Cyl.avgμ c) :=
          lintegral_const_mul' _ _ (by simp)
      _ ≤ 2 * ((∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) *
            (∫⁻ p, ‖g p‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^ (1 / (r / (r - 1)))) := by
          gcongr
          exact ENNReal.lintegral_mul_le_Lp_mul_Lq (Cyl.avgμ c) hpq
            hσ.enorm (hgc.measurable.enorm.aemeasurable)
      _ = _ := by rw [hAeq, hBeq]
  calc ENNReal.ofReal (σ ^ μ.re) * _ ≤ ENNReal.ofReal (σ ^ μ.re) *
        (2 * (dfA c r b σ * dfB c (r / (r - 1)) H (s - σ))) := by gcongr
    _ = _ := by ring

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.DualFPointwise_proof
