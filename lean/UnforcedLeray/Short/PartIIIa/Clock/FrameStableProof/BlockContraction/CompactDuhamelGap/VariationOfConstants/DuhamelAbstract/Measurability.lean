import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic

/-!
# Leaf A helper: Carathéodory composition with strongly measurable operator families

Helper for `PartIII-a:T21/c3/2/1/2/1` (`DuhamelVoCAbstract`, SP 2962-2982).

If `a ↦ T a x` is a.e. strongly measurable for every vector `x` (strong measurability of an
operator family, no measurability in operator norm) and `g` is a.e. strongly measurable, then
`a ↦ T a (g a)` is a.e. strongly measurable: approximate `g` by simple functions and pass to the
pointwise limit using the continuity of each `T a`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.DuhamelAbstractSub

/-- **Carathéodory composition**: a strongly measurable family of bounded operators applied to an
a.e. strongly measurable function is a.e. strongly measurable. -/
theorem aestronglyMeasurable_clm_apply {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] {T : α → E →L[ℂ] F} (hT : ∀ x, AEStronglyMeasurable (fun a => T a x) μ)
    {g : α → E} (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun a => T a (g a)) μ := by
  have hg' : StronglyMeasurable (hg.mk g) := hg.stronglyMeasurable_mk
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n a => T a (hg'.approx n a)) (fun n => ?_) ?_
  · have heq : (fun a => T a (hg'.approx n a)) = fun a =>
        ∑ y ∈ (hg'.approx n).range,
          ((hg'.approx n) ⁻¹' {y}).indicator (fun a => T a y) a := by
      funext a
      rw [Finset.sum_eq_single (hg'.approx n a)]
      · rw [Set.indicator_of_mem (by simp)]
      · intro y _ hy
        rw [Set.indicator_of_notMem]
        simpa [eq_comm] using hy
      · intro h
        exact absurd (SimpleFunc.mem_range_self _ a) h
    rw [heq]
    exact Finset.aestronglyMeasurable_fun_sum _ fun y _ =>
      (hT y).indicator ((hg'.approx n).measurableSet_fiber y)
  · filter_upwards [hg.ae_eq_mk] with a ha
    rw [ha]
    exact ((T a).continuous.tendsto _).comp (hg'.tendsto_approx a)

end UnforcedLeray.Short.IIIa.DuhamelAbstractSub
