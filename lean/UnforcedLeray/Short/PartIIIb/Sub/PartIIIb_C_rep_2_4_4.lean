import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4

/-!
# `PartIII-b:C/rep/2/4/4` : measurability of the vertical profile and of the reduced integral

Tonelli measurability (`Measurable.lintegral_prod_right'`) of `vprof g` and `vertRed a rIn D g`;
used for `annulusFubini` and `vertYoungPhase` (source 4164-4167, 5219-5221).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem measurable_vecSpace : Measurable (fun p : ℝ × ℝ × ℝ => (!₂[p.1, p.2.1, p.2.2] : Space)) := by
  apply Continuous.measurable
  fun_prop

theorem vertKern_measurable (rIn D : ℝ) : Measurable (vertKern rIn D) := by
  unfold vertKern
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

theorem vprof_measurable (g : ℝ → Space → ℝ≥0∞) (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (vprof g)) := by
  have h4 : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ => Function.uncurry g
      (p.1.1.1, (!₂[p.1.2, p.2, p.1.1.2] : Space))) := by
    refine hg.comp ?_
    refine (measurable_fst.fst.fst).prodMk ?_
    exact measurable_vecSpace.comp
      ((measurable_fst.snd).prodMk ((measurable_snd).prodMk (measurable_fst.fst.snd)))
  have h3 : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      ∫⁻ y : ℝ, Function.uncurry g (p.1.1, (!₂[p.2, y, p.1.2] : Space))) :=
    h4.lintegral_prod_right'
  have h2 : Measurable (fun p : ℝ × ℝ =>
      ∫⁻ x : ℝ, ∫⁻ y : ℝ, Function.uncurry g (p.1, (!₂[x, y, p.2] : Space))) :=
    h3.lintegral_prod_right'
  exact h2

theorem vertMeasurable : VertMeasurable := by
  intro g hg
  have hv := vprof_measurable g hg
  refine ⟨hv, fun a rIn D => ?_⟩
  unfold vertRed vertRedH
  have h1 : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
      vertKern rIn D (p.1.1.2 - p.1.2 * p.2) * vprof g (p.1.1.1 + 2 * Real.log p.1.2) p.2) := by
    refine Measurable.mul ?_ ?_
    · exact (vertKern_measurable rIn D).comp (by fun_prop)
    · exact hv.comp ((measurable_fst.fst.fst.add
        (measurable_const.mul (Real.measurable_log.comp measurable_fst.snd))).prodMk measurable_snd)
  have h2 : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal (p.2 ^ a) * ∫⁻ s : ℝ, vertKern rIn D (p.1.2 - p.2 * s) *
        vprof g (p.1.1 + 2 * Real.log p.2) s) := by
    refine Measurable.mul ?_ ?_
    · exact ENNReal.measurable_ofReal.comp (measurable_snd.pow_const a)
    · exact h1.lintegral_prod_right'
  exact h2.lintegral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) 1))

end UnforcedLeray.Short.PartIIIb.Concrete
