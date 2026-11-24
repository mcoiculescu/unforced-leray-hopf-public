import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressFlatLocalH14.SpatialHolderHalf.TestShift

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIa
open UnforcedLeray.B0220 UnforcedLeray.B0223 N05_4Aux N05_4_1Aux

namespace SHH

instance (c : ℝ) : SFinite (cellMeasure c) := by unfold cellMeasure; infer_instance

theorem integrable_comp_sj_real {c : ℝ} (hc : 0 < c) (j : Fin 2) (t : ℝ) {G : Profile → ℝ}
    (hG : Measurable G) (hper : QPeriodic c G) (hI : Integrable G (cellMeasure c)) :
    Integrable (fun p => G (sj j t p)) (cellMeasure c) := by
  have hnorm : ∫⁻ p, ‖G (sj j t p)‖ₑ ∂(cellMeasure c) = ∫⁻ p, ‖G p‖ₑ ∂(cellMeasure c) :=
    lintegral_sj_eq hc j t hG.enorm (fun p => by simp only [hper p])
  exact ⟨(hG.comp (measurable_sj j t)).aestronglyMeasurable, by
    unfold HasFiniteIntegral; rw [hnorm]; exact hI.2⟩

theorem memLp_comp_sj {c : ℝ} (hc : 0 < c) (j : Fin 2) (t : ℝ) {f : Profile → MeridC}
    (hm : Measurable f) (hper : QPeriodic c f) (hf : MemLp f 2 (cellMeasure c)) :
    MemLp (fun p => f (sj j t p)) 2 (cellMeasure c) := by
  have hms : Measurable (fun p => f (sj j t p)) := hm.comp (measurable_sj j t)
  rw [memLp_two_iff_integrable_sq_norm hms.aestronglyMeasurable]
  have h1 : Integrable (fun p => ‖f p‖ ^ 2) (cellMeasure c) :=
    (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  exact integrable_comp_sj_real hc j t (G := fun p => ‖f p‖ ^ 2) (hm.norm.pow_const 2)
    (fun p => by simp only [hper p]) h1

theorem integral_sq_comp_sj {c : ℝ} (hc : 0 < c) (j : Fin 2) (t : ℝ) {f : Profile → MeridC}
    (hm : Measurable f) (hper : QPeriodic c f) :
    ∫ p, ‖f (sj j t p)‖ ^ 2 ∂(cellMeasure c) = ∫ p, ‖f p‖ ^ 2 ∂(cellMeasure c) :=
  integral_sj_eq_real hc j t (G := fun p => ‖f p‖ ^ 2) (hm.norm.pow_const 2)
    (fun p => by simp only [hper p])

theorem int_norm_inner_le {c : ℝ} {f g : Profile → MeridC} (hf : MemLp f 2 (cellMeasure c))
    (hg : MemLp g 2 (cellMeasure c)) :
    ∫ p, ‖inner ℂ (f p) (g p)‖ ∂(cellMeasure c) ≤
      ((∫ p, ‖f p‖ ^ 2 ∂(cellMeasure c)) + ∫ p, ‖g p‖ ^ 2 ∂(cellMeasure c)) / 2 := by
  have hi1 : Integrable (fun p => ‖f p‖ ^ 2) (cellMeasure c) :=
    (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have hi2 : Integrable (fun p => ‖g p‖ ^ 2) (cellMeasure c) :=
    (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  calc ∫ p, ‖inner ℂ (f p) (g p)‖ ∂(cellMeasure c)
      ≤ ∫ p, (‖f p‖ ^ 2 + ‖g p‖ ^ 2) / 2 ∂(cellMeasure c) := by
        refine integral_mono (integrable_inner_cellMeasure hf hg).norm
          ((hi1.add hi2).div_const 2) (fun p => ?_)
        have := norm_inner_le_norm (𝕜 := ℂ) (f p) (g p)
        nlinarith [sq_nonneg (‖f p‖ - ‖g p‖), norm_nonneg (f p), norm_nonneg (g p)]
    _ = _ := by rw [integral_div, integral_add hi1 hi2]

/-- Fubini on `Ioc 0 h × cell`. -/
theorem fubini_swap {c h : ℝ} (F : ℝ → Profile → ℂ)
    (hFm : Measurable (fun tp : ℝ × Profile => F tp.1 tp.2))
    (hint : ∀ t ∈ Ioc 0 h, Integrable (F t) (cellMeasure c)) (C : ℝ)
    (hC : ∀ t ∈ Ioc 0 h, ∫ p, ‖F t p‖ ∂(cellMeasure c) ≤ C) :
    ∫ t in Ioc 0 h, ∫ p, F t p ∂(cellMeasure c) =
      ∫ p, (∫ t in Ioc 0 h, F t p) ∂(cellMeasure c) := by
  set ν : Measure ℝ := volume.restrict (Ioc 0 h) with hν
  have hfin : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have hAE : AEStronglyMeasurable (Function.uncurry F) (ν.prod (cellMeasure c)) :=
    hFm.aestronglyMeasurable
  have hI : Integrable (Function.uncurry F) (ν.prod (cellMeasure c)) := by
    rw [integrable_prod_iff hAE]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := h))] with t ht
      exact hint t ht
    · have hm2 : AEStronglyMeasurable (fun t => ∫ p, ‖Function.uncurry F (t, p)‖ ∂(cellMeasure c)) ν :=
        (hAE.norm).integral_prod_right'
      refine Integrable.mono' (integrable_const C) hm2 ?_
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := h))] with t ht
      rw [Real.norm_of_nonneg (integral_nonneg fun p => norm_nonneg _)]
      exact hC t ht
  exact integral_integral_swap hI

end SHH
end UnforcedLeray.Short.PartIIa
