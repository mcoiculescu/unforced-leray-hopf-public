import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2

/-!
# `ParamContDiff` (`PartIII-b:IIIb-D2/3/1/1/2/1`)

Differentiation under the integral sign, twice, via `hasFDerivAt_integral_of_dominated_of_fderiv_le`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem paramContDiff : ParamContDiff := by
  unfold ParamContDiff
  intro α _ m F U g hU hconv hC2 hg hb hmeas
  have hm0 : ∀ y ∈ U, AEStronglyMeasurable (fun a => F a y) m := by
    intro y hy
    have h := (continuousMultilinearCurryFin0 ℝ Space ℂ).continuous.comp_aestronglyMeasurable
      (hmeas 0 (by norm_num) y hy)
    refine h.congr (Filter.Eventually.of_forall fun a => ?_)
    simp [iteratedFDeriv_zero_eq_comp]
  have hcurry1 : ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℝ E'] (G : Space → E')
      (z : Space), continuousMultilinearCurryFin1 ℝ Space E' (iteratedFDeriv ℝ 1 G z) =
        fderiv ℝ G z := by
    intro E' _ _ G z
    ext v
    simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  have hm1 : ∀ y ∈ U, AEStronglyMeasurable (fun a => fderiv ℝ (F a) y) m := by
    intro y hy
    have h := (continuousMultilinearCurryFin1 ℝ Space ℂ).continuous.comp_aestronglyMeasurable
      (hmeas 1 (by norm_num) y hy)
    refine h.congr (Filter.Eventually.of_forall fun a => ?_)
    exact hcurry1 ℂ (F a) y
  have hcurry2 : ∀ a y, fderiv ℝ (fderiv ℝ (F a)) y =
      continuousMultilinearCurryFin1 ℝ Space (Space →L[ℝ] ℂ)
        (continuousMultilinearCurryRightEquiv' ℝ 1 Space ℂ (iteratedFDeriv ℝ (1 + 1) (F a) y)) := by
    intro a y
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
    exact (hcurry1 (Space →L[ℝ] ℂ) (fun z => fderiv ℝ (F a) z) y).symm
  have hm2 : ∀ y ∈ U, AEStronglyMeasurable (fun a => fderiv ℝ (fderiv ℝ (F a)) y) m := by
    intro y hy
    have hc : Continuous (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin (1 + 1) => Space) ℂ =>
        continuousMultilinearCurryFin1 ℝ Space (Space →L[ℝ] ℂ)
          (continuousMultilinearCurryRightEquiv' ℝ 1 Space ℂ T)) :=
      (continuousMultilinearCurryFin1 ℝ Space (Space →L[ℝ] ℂ)).continuous.comp
        (continuousMultilinearCurryRightEquiv' ℝ 1 Space ℂ).continuous
    have h := hc.comp_aestronglyMeasurable (hmeas (1 + 1) (by norm_num) y hy)
    refine h.congr (Filter.Eventually.of_forall fun a => ?_)
    exact (hcurry2 a y).symm
  have hB0 : ∀ᵐ a ∂m, ∀ y ∈ U, ‖F a y‖ ≤ g 0 a := by
    filter_upwards [hb 0 (by norm_num)] with a ha y hy
    simpa [norm_iteratedFDeriv_zero] using ha y hy
  have hB1 : ∀ᵐ a ∂m, ∀ y ∈ U, ‖fderiv ℝ (F a) y‖ ≤ g 1 a := by
    filter_upwards [hb 1 (by norm_num)] with a ha y hy
    simpa [norm_iteratedFDeriv_one] using ha y hy
  have hB2 : ∀ᵐ a ∂m, ∀ y ∈ U, ‖fderiv ℝ (fderiv ℝ (F a)) y‖ ≤ g (1 + 1) a := by
    filter_upwards [hb (1 + 1) (by norm_num)] with a ha y hy
    have e : ‖fderiv ℝ (fderiv ℝ (F a)) y‖ = ‖iteratedFDeriv ℝ (1 + 1) (F a) y‖ := by
      rw [← norm_iteratedFDeriv_one (f := fderiv ℝ (F a)), norm_iteratedFDeriv_fderiv]
    rw [e]
    exact ha y hy
  have hdiff1 : ∀ᵐ a ∂m, ∀ x ∈ U, HasFDerivAt (fun y => F a y) (fderiv ℝ (F a) x) x := by
    filter_upwards [hC2] with a ha x hx
    exact ((ha.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hC1 : ∀ᵐ a ∂m, ContDiffOn ℝ 1 (fderiv ℝ (F a)) U := by
    filter_upwards [hC2] with a ha
    exact ha.fderiv_of_isOpen (m := 1) hU (by norm_num)
  have hdiff2 : ∀ᵐ a ∂m, ∀ x ∈ U,
      HasFDerivAt (fun y => fderiv ℝ (F a) y) (fderiv ℝ (fderiv ℝ (F a)) x) x := by
    filter_upwards [hC1] with a ha x hx
    exact ((ha.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hcont2 : ∀ᵐ a ∂m, ContinuousOn (fun y => fderiv ℝ (fderiv ℝ (F a)) y) U := by
    filter_upwards [hC1] with a ha
    exact ha.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hint0 : ∀ y ∈ U, Integrable (fun a => F a y) m := fun y hy =>
    (hg 0 (by norm_num)).mono' (hm0 y hy) (hB0.mono fun a ha => ha y hy)
  have hint1 : ∀ y ∈ U, Integrable (fun a => fderiv ℝ (F a) y) m := fun y hy =>
    (hg 1 (by norm_num)).mono' (hm1 y hy) (hB1.mono fun a ha => ha y hy)
  have hD1 : ∀ y ∈ U, HasFDerivAt (fun y => ∫ a, F a y ∂m) (∫ a, fderiv ℝ (F a) y ∂m) y := by
    intro y hy
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun y a => F a y)
      (F' := fun y a => fderiv ℝ (F a) y) (bound := g 1) (hU.mem_nhds hy)
      (Filter.eventually_of_mem (hU.mem_nhds hy) fun y' hy' => hm0 y' hy')
      (hint0 y hy) (hm1 y hy) hB1 (hg 1 (by norm_num)) hdiff1
  have hD2 : ∀ y ∈ U, HasFDerivAt (fun y => ∫ a, fderiv ℝ (F a) y ∂m)
      (∫ a, fderiv ℝ (fderiv ℝ (F a)) y ∂m) y := by
    intro y hy
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun y a => fderiv ℝ (F a) y)
      (F' := fun y a => fderiv ℝ (fderiv ℝ (F a)) y) (bound := g (1 + 1)) (hU.mem_nhds hy)
      (Filter.eventually_of_mem (hU.mem_nhds hy) fun y' hy' => hm1 y' hy')
      (hint1 y hy) (hm2 y hy) hB2 (hg (1 + 1) (by norm_num)) hdiff2
  have hcontD2 : ContinuousOn (fun y => ∫ a, fderiv ℝ (fderiv ℝ (F a)) y ∂m) U :=
    continuousOn_of_dominated (F := fun y a => fderiv ℝ (fderiv ℝ (F a)) y)
      (fun y hy => hm2 y hy) (fun y hy => hB2.mono fun a ha => ha y hy)
      (hg (1 + 1) (by norm_num)) hcont2
  have hψC1 : ContDiffOn ℝ 1 (fun y => ∫ a, fderiv ℝ (F a) y ∂m) U := by
    have h := (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hU).2
      ⟨fun y hy => (hD2 y hy).differentiableAt.differentiableWithinAt,
       fun h0 => absurd h0 (by simp),
       contDiffOn_zero.2 (hcontD2.congr fun y hy => (hD2 y hy).fderiv)⟩
    simpa using h
  have hΦC2 : ContDiffOn ℝ 2 (fun y => ∫ a, F a y ∂m) U := by
    have h := (contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) hU).2
      ⟨fun y hy => (hD1 y hy).differentiableAt.differentiableWithinAt,
       fun h1 => absurd h1 (by simp),
       hψC1.congr fun y hy => (hD1 y hy).fderiv⟩
    exact h
  exact hΦC2

end UnforcedLeray.Short.PartIIIb.Concrete
