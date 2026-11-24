import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_3

/-!
# `ParamHasFDeriv1` (`PartIII-b:C/rep/2/6/3/3/8`)

First-order differentiation under the integral sign: the first half of `paramContDiff`
(`IIIb-D2_3_1_1_2/L1.lean`), via `hasFDerivAt_integral_of_dominated_of_fderiv_le`.
Source 3603-3626, 3800-3807, 4171-4200, 5223.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem paramHasFDeriv1 : ParamHasFDeriv1 := by
  unfold ParamHasFDeriv1
  intro α _ m F U g hU hconv hg hb hmeas y hy
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
  have hB0 : ∀ᵐ a ∂m, ∀ y ∈ U, ‖F a y‖ ≤ g 0 a := by
    filter_upwards [hb 0 (by norm_num)] with a ha y hy
    simpa [norm_iteratedFDeriv_zero] using ha y hy
  have hB1 : ∀ᵐ a ∂m, ∀ y ∈ U, ‖fderiv ℝ (F a) y‖ ≤ g 1 a := by
    filter_upwards [hb 1 (by norm_num)] with a ha y hy
    simpa [norm_iteratedFDeriv_one] using ha y hy
  have hdiff1 : ∀ᵐ a ∂m, ∀ x ∈ U, HasFDerivAt (fun y => F a y) (fderiv ℝ (F a) x) x := by
    filter_upwards [hconv] with a ha x hx
    exact ((ha.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hint0 : Integrable (fun a => F a y) m :=
    (hg 0 (by norm_num)).mono' (hm0 y hy) (hB0.mono fun a ha => ha y hy)
  have hint1 : Integrable (fun a => fderiv ℝ (F a) y) m :=
    (hg 1 (by norm_num)).mono' (hm1 y hy) (hB1.mono fun a ha => ha y hy)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun y a => F a y)
    (F' := fun y a => fderiv ℝ (F a) y) (bound := g 1) (hU.mem_nhds hy)
    (Filter.eventually_of_mem (hU.mem_nhds hy) fun y' hy' => hm0 y' hy')
    hint0 (hm1 y hy) hB1 (hg 1 (by norm_num)) hdiff1

end UnforcedLeray.Short.PartIIIb.Concrete
