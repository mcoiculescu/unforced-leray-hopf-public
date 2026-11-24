import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5

/-!
# Measurability of the separated majorant (`PartIII-b:IIIb-D2/3/1/1/2/5/1`)

`(l,z) ↦ l^{2 Re μ + 2} (1 + l|z|)^{-4-n} |T(τ + 2 log l, z)|` is measurable, since `T` is jointly
measurable (`IsSepSource.measurable`) and the remaining operations are measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem l5Meas : L5Meas := by
  intro μ P rOut T hS τ n
  have hm : ∀ i j, Measurable fun p : ℝ × Space => T (τ + 2 * Real.log p.1) p.2 i j := by
    intro i j
    have hq : Measurable fun p : ℝ × Space => (τ + 2 * Real.log p.1, p.2) :=
      (measurable_const.add (measurable_const.mul (Real.measurable_log.comp measurable_fst))).prodMk
        measurable_snd
    exact (hS.measurable i j).comp hq
  have hsum : Measurable fun p : ℝ × Space => ∑ i : Fin 3, ∑ j : Fin 3,
      T (τ + 2 * Real.log p.1) p.2 i j ^ 2 :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => (hm i j).pow_const 2
  have hten : Measurable fun p : ℝ × Space => IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2) := by
    unfold IIIa.tensorNorm
    exact Real.continuous_sqrt.measurable.comp hsum
  unfold sepMajorant
  refine ((measurable_fst.pow_const _).mul ?_).mul hten
  exact (((measurable_const.add (measurable_fst.mul measurable_snd.norm))).pow_const _)

end UnforcedLeray.Short.PartIIIb.Concrete
