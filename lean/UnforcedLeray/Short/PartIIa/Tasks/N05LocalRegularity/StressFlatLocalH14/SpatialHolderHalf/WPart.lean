import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressFlatLocalH14.SpatialHolderHalf.Fub

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIa
open UnforcedLeray.B0220 UnforcedLeray.B0223 N05_4Aux N05_4_1Aux

namespace SHH

/-- the time-averaged shift `W p = ∫_{(0,h]} dq (p + t e_j) dt` -/
def Wd (j : Fin 2) (h : ℝ) (dq : Profile → MeridC) (p : Profile) : MeridC :=
  ∫ t in Ioc (0 : ℝ) h, dq (sj j t p)

/-- Cauchy-Schwarz on `Ioc 0 h`. -/
theorem cs_real {h : ℝ} (hh : 0 < h) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) h))) :
    (∫ t in Ioc (0 : ℝ) h, g t) ^ 2 ≤ h * ∫ t in Ioc (0 : ℝ) h, g t ^ 2 := by
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) h) with hν
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have hg1 : Integrable g ν := hg.integrable (by norm_num)
  have hg2 : Integrable (fun t => g t ^ 2) ν := hg.integrable_sq
  have hvol : ν.real univ = h := by
    simp [hν, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc, hh.le]
  have key : ∀ a : ℝ, 0 ≤ (∫ t, g t ^ 2 ∂ν) - 2 * a * (∫ t, g t ∂ν) + a ^ 2 * h := by
    intro a
    have : ∫ t, (g t - a) ^ 2 ∂ν = (∫ t, g t ^ 2 ∂ν) - 2 * a * (∫ t, g t ∂ν) + a ^ 2 * h := by
      have e : ∀ t, (g t - a) ^ 2 = (g t ^ 2 - 2 * a * g t) + a ^ 2 := fun t => by ring
      simp_rw [e]
      have i1 : Integrable (fun t => g t ^ 2 - 2 * a * g t) ν := hg2.sub (hg1.const_mul (2 * a))
      rw [integral_add (f := fun t => g t ^ 2 - 2 * a * g t) (g := fun _ => a ^ 2) i1
        (integrable_const _),
        integral_sub (f := fun t => g t ^ 2) (g := fun t => 2 * a * g t) hg2
          (hg1.const_mul (2 * a)), integral_const_mul, integral_const, hvol]
      simp; ring
    rw [← this]
    exact integral_nonneg fun t => sq_nonneg _
  have := key ((∫ t, g t ∂ν) / h)
  have hne : h ≠ 0 := hh.ne'
  have e2 : (∫ t, g t ^ 2 ∂ν) - 2 * ((∫ t, g t ∂ν) / h) * (∫ t, g t ∂ν) +
      ((∫ t, g t ∂ν) / h) ^ 2 * h = (∫ t, g t ^ 2 ∂ν) - (∫ t, g t ∂ν) ^ 2 / h := by
    field_simp; ring
  rw [e2, sub_nonneg, div_le_iff₀ hh] at this
  nlinarith

theorem lintegral_E {c : ℝ} (hc : 0 < c) (j : Fin 2) {h : ℝ} {dq : Profile → MeridC}
    (hm : Measurable dq) (hper : QPeriodic c dq) :
    ∫⁻ p, (∫⁻ t in Ioc (0 : ℝ) h, ‖dq (sj j t p)‖ₑ ^ 2) ∂(cellMeasure c) =
      ENNReal.ofReal h * ∫⁻ p, ‖dq p‖ₑ ^ 2 ∂(cellMeasure c) := by
  have hf : Measurable (fun pt : Profile × ℝ => ‖dq (sj j pt.2 pt.1)‖ₑ ^ 2) := by
    have : Measurable (fun pt : Profile × ℝ => dq (sj j pt.2 pt.1)) :=
      hm.comp ((measurable_sj_uncurry j).comp (measurable_snd.prodMk measurable_fst))
    exact this.enorm.pow_const 2
  rw [lintegral_lintegral_swap (f := fun p t => ‖dq (sj j t p)‖ₑ ^ 2) hf.aemeasurable]
  have : ∀ t : ℝ, ∫⁻ p, ‖dq (sj j t p)‖ₑ ^ 2 ∂(cellMeasure c) =
      ∫⁻ p, ‖dq p‖ₑ ^ 2 ∂(cellMeasure c) := fun t =>
    lintegral_sj_eq hc j t (f := fun p => ‖dq p‖ₑ ^ 2) (hm.enorm.pow_const 2)
      (fun p => by simp only [hper p])
  simp_rw [this]
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc,
    sub_zero, mul_comm]

theorem measurable_dq_sj {j : Fin 2} {dq : Profile → MeridC} (hm : Measurable dq) (p : Profile) :
    Measurable (fun t : ℝ => dq (sj j t p)) :=
  hm.comp ((measurable_sj_uncurry j).comp (measurable_id.prodMk measurable_const))

theorem enorm_sq_eq (x : MeridC) : ‖(‖x‖ ^ 2)‖ₑ = ‖x‖ₑ ^ 2 := by
  rw [enorm_pow, enorm_norm]

theorem lintegral_sq_lt_top {c : ℝ} {dq : Profile → MeridC} (hm : Measurable dq)
    (hL : MemLp dq 2 (cellMeasure c)) : ∫⁻ p, ‖dq p‖ₑ ^ 2 ∂(cellMeasure c) < ⊤ := by
  have hI := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hL
  have := hI.2
  unfold HasFiniteIntegral at this
  simpa only [enorm_sq_eq] using this

theorem ae_good {c : ℝ} (hc : 0 < c) (j : Fin 2) {h : ℝ} {dq : Profile → MeridC}
    (hm : Measurable dq) (hper : QPeriodic c dq) (hL : MemLp dq 2 (cellMeasure c)) :
    ∀ᵐ p ∂(cellMeasure c), ∫⁻ t in Ioc (0 : ℝ) h, ‖dq (sj j t p)‖ₑ ^ 2 < ⊤ := by
  have hE := lintegral_E hc j (h := h) hm hper
  have hf : Measurable (fun pt : Profile × ℝ => ‖dq (sj j pt.2 pt.1)‖ₑ ^ 2) := by
    have : Measurable (fun pt : Profile × ℝ => dq (sj j pt.2 pt.1)) :=
      hm.comp ((measurable_sj_uncurry j).comp (measurable_snd.prodMk measurable_fst))
    exact this.enorm.pow_const 2
  have hmeas : Measurable (fun p => ∫⁻ t in Ioc (0 : ℝ) h, ‖dq (sj j t p)‖ₑ ^ 2) :=
    hf.lintegral_prod_right'
  refine ae_lt_top hmeas ?_
  rw [hE]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_sq_lt_top hm hL).ne

theorem good_bound {j : Fin 2} {h : ℝ} (hh : 0 < h) {dq : Profile → MeridC} (hm : Measurable dq)
    (p : Profile) (hp : ∫⁻ t in Ioc (0 : ℝ) h, ‖dq (sj j t p)‖ₑ ^ 2 < ⊤) :
    Integrable (fun t => dq (sj j t p)) (volume.restrict (Ioc (0 : ℝ) h)) ∧
    ‖Wd j h dq p‖ₑ ^ 2 ≤ ENNReal.ofReal h * ∫⁻ t in Ioc (0 : ℝ) h, ‖dq (sj j t p)‖ₑ ^ 2 := by
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) h) with hν
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have hms := measurable_dq_sj (j := j) hm p
  have hI2 : Integrable (fun t => ‖dq (sj j t p)‖ ^ 2) ν := by
    refine ⟨(hms.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simpa only [enorm_sq_eq] using hp
  have hmem : MemLp (fun t => dq (sj j t p)) 2 ν :=
    (memLp_two_iff_integrable_sq_norm hms.aestronglyMeasurable).2 hI2
  refine ⟨hmem.integrable (by norm_num), ?_⟩
  have hg : MemLp (fun t => ‖dq (sj j t p)‖) 2 ν := hmem.norm
  have hcs := cs_real hh hg
  have hnorm : ‖Wd j h dq p‖ ≤ ∫ t in Ioc (0 : ℝ) h, ‖dq (sj j t p)‖ := norm_integral_le_integral_norm _
  have hsq : ‖Wd j h dq p‖ ^ 2 ≤ h * ∫ t in Ioc (0 : ℝ) h, ‖dq (sj j t p)‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcs
  have h1 : ‖Wd j h dq p‖ₑ ^ 2 = ENNReal.ofReal (‖Wd j h dq p‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have h2 : ∫⁻ t in Ioc (0 : ℝ) h, ‖dq (sj j t p)‖ₑ ^ 2 =
      ENNReal.ofReal (∫ t in Ioc (0 : ℝ) h, ‖dq (sj j t p)‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hI2 (Eventually.of_forall fun t => sq_nonneg _)]
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rw [h1, h2, ← ENNReal.ofReal_mul hh.le]
  exact ENNReal.ofReal_le_ofReal hsq

theorem lintegral_W_le {c : ℝ} (hc : 0 < c) (j : Fin 2) {h : ℝ} (hh : 0 < h)
    {dq : Profile → MeridC} (hm : Measurable dq) (hper : QPeriodic c dq)
    (hL : MemLp dq 2 (cellMeasure c)) :
    ∫⁻ p, ‖Wd j h dq p‖ₑ ^ 2 ∂(cellMeasure c) ≤
      ENNReal.ofReal h * (ENNReal.ofReal h * ∫⁻ p, ‖dq p‖ₑ ^ 2 ∂(cellMeasure c)) := by
  calc ∫⁻ p, ‖Wd j h dq p‖ₑ ^ 2 ∂(cellMeasure c)
      ≤ ∫⁻ p, ENNReal.ofReal h * (∫⁻ t in Ioc (0 : ℝ) h, ‖dq (sj j t p)‖ₑ ^ 2) ∂(cellMeasure c) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_good hc j (h := h) hm hper hL] with p hp
        exact (good_bound hh hm p hp).2
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_E hc j hm hper]

theorem stronglyMeasurable_W (j : Fin 2) (h : ℝ) {dq : Profile → MeridC} (hm : Measurable dq) :
    StronglyMeasurable (Wd j h dq) := by
  have hf : StronglyMeasurable (Function.uncurry fun (p : Profile) (t : ℝ) => dq (sj j t p)) := by
    have : Measurable (Function.uncurry fun (p : Profile) (t : ℝ) => dq (sj j t p)) :=
      hm.comp ((measurable_sj_uncurry j).comp (measurable_snd.prodMk measurable_fst))
    exact this.stronglyMeasurable
  exact hf.integral_prod_right (ν := volume.restrict (Ioc (0 : ℝ) h))

theorem memLp_W {c : ℝ} (hc : 0 < c) (j : Fin 2) {h : ℝ} (hh : 0 < h)
    {dq : Profile → MeridC} (hm : Measurable dq) (hper : QPeriodic c dq)
    (hL : MemLp dq 2 (cellMeasure c)) : MemLp (Wd j h dq) 2 (cellMeasure c) := by
  have hms := (stronglyMeasurable_W j h hm).measurable
  rw [memLp_two_iff_integrable_sq_norm hms.aestronglyMeasurable]
  refine ⟨(hms.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simp only [enorm_sq_eq]
  refine lt_of_le_of_lt (lintegral_W_le hc j hh hm hper hL) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_sq_lt_top hm hL))

theorem integral_W_le {c : ℝ} (hc : 0 < c) (j : Fin 2) {h : ℝ} (hh : 0 < h)
    {dq : Profile → MeridC} (hm : Measurable dq) (hper : QPeriodic c dq)
    (hL : MemLp dq 2 (cellMeasure c)) :
    ∫ p, ‖Wd j h dq p‖ ^ 2 ∂(cellMeasure c) ≤ h ^ 2 * ∫ p, ‖dq p‖ ^ 2 ∂(cellMeasure c) := by
  have hIW := (memLp_two_iff_integrable_sq_norm (stronglyMeasurable_W j h hm).measurable.aestronglyMeasurable).1
    (memLp_W hc j hh hm hper hL)
  have hId := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hL
  have e1 : ∫ p, ‖Wd j h dq p‖ ^ 2 ∂(cellMeasure c) =
      (∫⁻ p, ‖Wd j h dq p‖ₑ ^ 2 ∂(cellMeasure c)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun p => sq_nonneg _) hIW.1]
    congr 1
    refine lintegral_congr fun p => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have e2 : ∫⁻ p, ‖dq p‖ₑ ^ 2 ∂(cellMeasure c) = ENNReal.ofReal (∫ p, ‖dq p‖ ^ 2 ∂(cellMeasure c)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hId (Eventually.of_forall fun p => sq_nonneg _)]
    refine lintegral_congr fun p => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hnn : 0 ≤ ∫ p, ‖dq p‖ ^ 2 ∂(cellMeasure c) := integral_nonneg fun p => sq_nonneg _
  have hle : ∫⁻ p, ‖Wd j h dq p‖ₑ ^ 2 ∂(cellMeasure c) ≤
      ENNReal.ofReal (h ^ 2 * ∫ p, ‖dq p‖ ^ 2 ∂(cellMeasure c)) := by
    refine (lintegral_W_le hc j hh hm hper hL).trans (le_of_eq ?_)
    rw [e2, ← ENNReal.ofReal_mul hh.le, ← ENNReal.ofReal_mul hh.le]
    congr 1; ring
  rw [e1]
  calc _ ≤ (ENNReal.ofReal (h ^ 2 * ∫ p, ‖dq p‖ ^ 2 ∂(cellMeasure c))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = _ := ENNReal.toReal_ofReal (by positivity)

end SHH
end UnforcedLeray.Short.PartIIa
