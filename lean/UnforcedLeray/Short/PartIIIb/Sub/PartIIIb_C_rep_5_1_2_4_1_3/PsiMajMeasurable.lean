import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/2`: joint measurability of the majorant

Source `the November 2 reference manuscript` 3611-3621, 5588-5589 (the majorant
`psiMaj` is an iterated integral of the measurable kernel `1_{ϱ(z)<θϱ(y)} |y-λz|^{-4} srcW`).
Proves `PsiMajMeasurable`: write `psiMaj` as the iterated integral of one measurable function
`H(((x, l), z))` (indicator form of the radial gap), then apply `Measurable.lintegral_prod_right'`
twice (over `z` with `volume`, then over `l` with `volume.restrict (Ioo 0 1)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

theorem psiMajMeasurable : PsiMajMeasurable := by
  intro R c θ G hG
  obtain ⟨H, hHdef⟩ : ∃ H : ((ℝ × Space) × ℝ) × Space → ℝ≥0∞, H = fun q =>
      if ϱ q.2 < θ * ϱ q.1.1.2 then
        ENNReal.ofReal ((‖q.1.1.2 - q.1.2 • q.2‖ ^ 4)⁻¹) *
          srcW R c G (q.1.1.1 + 2 * Real.log q.1.2) q.2
      else 0 := ⟨_, rfl⟩
  have hH : Measurable H := by
    rw [hHdef]
    refine Measurable.ite ?_ ?_ ?_
    · exact measurableSet_lt (measurable_ϱ.comp measurable_snd)
        (measurable_const.mul (measurable_ϱ.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))))
    · apply Measurable.mul
      · have hd : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.1.1.2 - q.1.2 • q.2) :=
          (measurable_snd.comp (measurable_fst.comp measurable_fst)).sub
            ((measurable_snd.comp measurable_fst).smul measurable_snd)
        exact ENNReal.measurable_ofReal.comp (((measurable_norm.comp hd).pow_const 4).inv)
      · have hφ : Measurable (fun q : ((ℝ × Space) × ℝ) × Space =>
            (q.1.1.1 + 2 * Real.log q.1.2, q.2)) :=
          ((measurable_fst.comp (measurable_fst.comp measurable_fst)).add
            (measurable_const.mul (Real.measurable_log.comp (measurable_snd.comp measurable_fst))))
            |>.prodMk measurable_snd
        have hsrc : Measurable (fun a : ℝ × Space => srcW R c G a.1 a.2) := measurable_srcW R c hG
        have h2 := hsrc.comp hφ
        exact h2
    · exact measurable_const
  have hS : ∀ x : ℝ × Space, MeasurableSet {z : Space | ϱ z < θ * ϱ x.2} :=
    fun x => measurableSet_lt measurable_ϱ measurable_const
  have hfun : (fun x : ℝ × Space => psiMaj R c θ G x.1 x.2) =
      fun x => ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z, H ((x, l), z) := by
    funext x
    unfold psiMaj
    refine lintegral_congr fun l => ?_
    rw [← lintegral_indicator (hS x)]
    refine lintegral_congr fun z => ?_
    simp [hHdef, Set.indicator_apply]
  show Measurable (fun x : ℝ × Space => psiMaj R c θ G x.1 x.2)
  rw [hfun]
  have g1 : Measurable (fun a : (ℝ × Space) × ℝ => ∫⁻ z, H (a, z)) :=
    hH.lintegral_prod_right'
  exact g1.lintegral_prod_right'

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
