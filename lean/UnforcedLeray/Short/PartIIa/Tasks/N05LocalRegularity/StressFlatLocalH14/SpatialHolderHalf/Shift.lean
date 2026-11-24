import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_4_1

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIa
open UnforcedLeray.B0220 N05_4Aux N05_4_1Aux

namespace SHH

/-- shift by `t` in the spatial direction `j` (`0` = q, `1` = η). -/
def sj (j : Fin 2) (t : ℝ) (p : Profile) : Profile :=
  p + t • ((0 : ℝ), UnforcedLeray.B0579.dir j)

theorem sj_zero_eq (t : ℝ) : sj 0 t = shiftQ t := by
  funext p; ext <;> simp [sj, shiftQ, UnforcedLeray.B0579.dir]

theorem sj_one_eq (t : ℝ) : sj 1 t = shiftEta t := by
  funext p; ext <;> simp [sj, shiftEta, UnforcedLeray.B0579.dir]

theorem sj_zero_t (j : Fin 2) (p : Profile) : sj j 0 p = p := by simp [sj]

theorem sj_add (j : Fin 2) (s t : ℝ) (p : Profile) : sj j s (sj j t p) = sj j (t + s) p := by
  simp only [sj, add_smul, add_assoc]

theorem sj_neg_sj (j : Fin 2) (t : ℝ) (p : Profile) : sj j (-t) (sj j t p) = p := by
  rw [sj_add]; simp [sj_zero_t]

theorem sj_sj_neg (j : Fin 2) (t : ℝ) (p : Profile) : sj j t (sj j (-t) p) = p := by
  rw [sj_add]; simp [sj_zero_t]

theorem sj_fst (j : Fin 2) (t : ℝ) (p : Profile) : (sj j t p).1 = p.1 := by
  fin_cases j <;> simp [sj, UnforcedLeray.B0579.dir]

theorem measurable_sj_uncurry (j : Fin 2) :
    Measurable (fun tp : ℝ × Profile => sj j tp.1 tp.2) := by
  unfold sj
  fin_cases j
  · have := measurable_shiftQ_uncurry
    convert this using 2 with tp
    ext <;> simp [shiftQ, UnforcedLeray.B0579.dir]
  · have := measurable_shiftEta_uncurry
    convert this using 2 with tp
    ext <;> simp [shiftEta, UnforcedLeray.B0579.dir]

theorem measurable_sj (j : Fin 2) (t : ℝ) : Measurable (sj j t) :=
  (measurable_sj_uncurry j).comp (measurable_const.prodMk measurable_id)

theorem continuous_sj (j : Fin 2) (t : ℝ) : Continuous (sj j t) := by
  unfold sj; fun_prop

theorem periodic_sj_comp {c : ℝ} {E : Type*} (j : Fin 2) (t : ℝ) {f : Profile → E}
    (hf : QPeriodic c f) : QPeriodic c (fun p => f (sj j t p)) := by
  intro p
  have : sj j t (p.1, p.2.1 + c, p.2.2) = ((sj j t p).1, (sj j t p).2.1 + c, (sj j t p).2.2) := by
    fin_cases j <;> simp [sj, UnforcedLeray.B0579.dir] <;> ring
  simp only [this]
  exact hf _

theorem lintegral_sj_eq {c : ℝ} (hc : 0 < c) (j : Fin 2) (t : ℝ) {f : Profile → ℝ≥0∞}
    (hf : Measurable f) (hper : QPeriodic c f) :
    ∫⁻ p, f (sj j t p) ∂(cellMeasure c) = ∫⁻ p, f p ∂(cellMeasure c) := by
  fin_cases j
  · simpa [sj_zero_eq] using lintegral_shiftQ_eq hc t hf hper
  · simpa [sj_one_eq] using lintegral_shiftEta_eq c t hf

/-- real-valued Bochner invariance -/
theorem integral_sj_eq_real {c : ℝ} (hc : 0 < c) (j : Fin 2) (t : ℝ) {G : Profile → ℝ}
    (hG : Measurable G) (hper : QPeriodic c G) :
    ∫ p, G (sj j t p) ∂(cellMeasure c) = ∫ p, G p ∂(cellMeasure c) := by
  have hGs : Measurable (fun p => G (sj j t p)) := hG.comp (measurable_sj j t)
  have hpers : QPeriodic c (fun p => G (sj j t p)) := periodic_sj_comp j t hper
  have hnorm : ∫⁻ p, ‖G (sj j t p)‖ₑ ∂(cellMeasure c) = ∫⁻ p, ‖G p‖ₑ ∂(cellMeasure c) :=
    lintegral_sj_eq hc j t hG.enorm (fun p => by simp only [hper p])
  by_cases hI : Integrable G (cellMeasure c)
  · have hI' : Integrable (fun p => G (sj j t p)) (cellMeasure c) :=
      ⟨hGs.aestronglyMeasurable, by
        unfold HasFiniteIntegral; rw [hnorm]; exact hI.2⟩
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI',
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI]
    have h1 := lintegral_sj_eq hc j t (f := fun p => ENNReal.ofReal (G p))
      (ENNReal.measurable_ofReal.comp hG) (fun p => by simp only [hper p])
    have h2 := lintegral_sj_eq hc j t (f := fun p => ENNReal.ofReal (-G p))
      (ENNReal.measurable_ofReal.comp hG.neg) (fun p => by simp only [hper p])
    rw [h1, h2]
  · have hI' : ¬ Integrable (fun p => G (sj j t p)) (cellMeasure c) := by
      intro h
      apply hI
      refine ⟨hG.aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral; rw [← hnorm]; exact h.2
    rw [integral_undef hI, integral_undef hI']

/-- complex-valued Bochner invariance -/
theorem integral_sj_eq {c : ℝ} (hc : 0 < c) (j : Fin 2) (t : ℝ) {G : Profile → ℂ}
    (hG : Measurable G) (hper : QPeriodic c G) :
    ∫ p, G (sj j t p) ∂(cellMeasure c) = ∫ p, G p ∂(cellMeasure c) := by
  have hGs : Measurable (fun p => G (sj j t p)) := hG.comp (measurable_sj j t)
  have hnorm : ∫⁻ p, ‖G (sj j t p)‖ₑ ∂(cellMeasure c) = ∫⁻ p, ‖G p‖ₑ ∂(cellMeasure c) :=
    lintegral_sj_eq hc j t hG.enorm (fun p => by simp only [hper p])
  by_cases hI : Integrable G (cellMeasure c)
  · have hI' : Integrable (fun p => G (sj j t p)) (cellMeasure c) :=
      ⟨hGs.aestronglyMeasurable, by
        unfold HasFiniteIntegral; rw [hnorm]; exact hI.2⟩
    apply Complex.ext
    · have e1 := integral_re hI'
      have e2 := integral_re hI
      try simp only [RCLike.re_to_complex] at e1 e2
      rw [← e1, ← e2]
      exact integral_sj_eq_real hc j t (Complex.measurable_re.comp hG)
        (fun p => by simp [hper p])
    · have e1 := integral_im hI'
      have e2 := integral_im hI
      try simp only [RCLike.im_to_complex] at e1 e2
      rw [← e1, ← e2]
      exact integral_sj_eq_real hc j t (Complex.measurable_im.comp hG)
        (fun p => by simp [hper p])
  · have hI' : ¬ Integrable (fun p => G (sj j t p)) (cellMeasure c) := by
      intro h
      apply hI
      refine ⟨hG.aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral; rw [← hnorm]; exact h.2
    rw [integral_undef hI, integral_undef hI']

end SHH
end UnforcedLeray.Short.PartIIa
