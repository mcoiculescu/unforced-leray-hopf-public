import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/3`: joint measurability of `phKer · srcW`

Source `the November 2 reference manuscript` (measurability for Minkowski).
`phKer` is an `if` on the measurable set `{σ < τ ∧ ϱ z < θ ϱ y}`; the source weight is
`measurable_srcW` composed with the snd projection.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- Joint measurability of `phKer · srcW` in output and atom. -/
theorem kerSrcMeasurable : KerSrcMeasurable := by
  intro R c θ G hG
  have hsrc : Measurable (fun q : (ℝ × Space) × (ℝ × Space) => srcW R c G q.2.1 q.2.2) :=
    (measurable_srcW R c hG).comp measurable_snd
  have hcond : MeasurableSet {q : (ℝ × Space) × (ℝ × Space) |
      q.2.1 < q.1.1 ∧ ϱ q.2.2 < θ * ϱ q.1.2} := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt (measurable_fst.comp measurable_snd)
        (measurable_fst.comp measurable_fst)
    · exact measurableSet_lt (measurable_ϱ.comp (measurable_snd.comp measurable_snd))
        ((measurable_const.mul (measurable_ϱ.comp (measurable_snd.comp measurable_fst))))
  have hf : Measurable (fun q : (ℝ × Space) × (ℝ × Space) =>
      ENNReal.ofReal (Real.exp ((q.2.1 - q.1.1) / 2) / 2) *
        ENNReal.ofReal ((‖q.1.2 - Real.exp ((q.2.1 - q.1.1) / 2) • q.2.2‖ ^ 4)⁻¹)) := by
    have h1 : Measurable (fun q : (ℝ × Space) × (ℝ × Space) =>
        Real.exp ((q.2.1 - q.1.1) / 2) / 2) := by fun_prop
    have h2 : Measurable (fun q : (ℝ × Space) × (ℝ × Space) =>
        (‖q.1.2 - Real.exp ((q.2.1 - q.1.1) / 2) • q.2.2‖ ^ 4)⁻¹) := by fun_prop
    exact h1.ennreal_ofReal.mul h2.ennreal_ofReal
  have hker : Measurable (fun q : (ℝ × Space) × (ℝ × Space) =>
      phKer θ q.1.1 q.1.2 q.2.1 q.2.2) := by
    unfold phKer
    exact Measurable.ite (p := fun q : (ℝ × Space) × (ℝ × Space) =>
        q.2.1 < q.1.1 ∧ ϱ q.2.2 < θ * ϱ q.1.2) hcond hf measurable_const
  exact hker.mul hsrc

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
