import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Order.Filter.AtTopBot.Interval
import Mathlib.Order.Interval.Finset.Box
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! `PartIII-a:T23/9/2/2`: a `ℤ`-indexed `tsum` of measurable complex functions is measurable. -/

set_option autoImplicit false

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.T23_9_Sub

theorem measurable_ztsum {X : Type*} [MeasurableSpace X] (F : ℤ → X → ℂ)
    (hF : ∀ k, Measurable (F k)) : Measurable (fun x => ∑' k : ℤ, F k x) := by
  classical
  have hE : Measurable (fun x => ∑' k : ℤ, (‖F k x‖₊ : ENNReal)) :=
    Measurable.ennreal_tsum (fun k => (hF k).nnnorm.coe_nnreal_ennreal)
  have hS : MeasurableSet {x | Summable (fun k : ℤ => F k x)} := by
    have : {x | Summable (fun k : ℤ => F k x)} =
        {x | (∑' k : ℤ, (‖F k x‖₊ : ENNReal)) ≠ ⊤} := by
      ext x
      simp only [mem_setOf_eq]
      rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
      exact summable_norm_iff.symm
    rw [this]
    exact hE (measurableSet_singleton ⊤).compl
  let g : ℕ → X → ℂ := fun n x =>
    {x | Summable (fun k : ℤ => F k x)}.indicator
      (fun x => ∑ k ∈ Finset.Icc (-(n : ℤ)) n, F k x) x
  refine measurable_of_tendsto_metrizable (f := g) (fun n => ?_) ?_
  · exact (Finset.measurable_sum _ (fun k _ => hF k)).indicator hS
  · rw [tendsto_pi_nhds]
    intro x
    by_cases hx : Summable (fun k : ℤ => F k x)
    · have h1 : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc (-(n : ℤ)) n, F k x) atTop
          (𝓝 (∑' k : ℤ, F k x)) :=
        hx.hasSum.comp (Finset.tendsto_Icc_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop)
      refine h1.congr (fun n => ?_)
      simp [g, hx]
    · have h0 : ∑' k : ℤ, F k x = 0 := tsum_eq_zero_of_not_summable hx
      rw [h0]
      refine tendsto_const_nhds.congr (fun n => ?_)
      simp [g, hx]

end UnforcedLeray.Short.IIIa.T23_9_Sub

#print axioms UnforcedLeray.Short.IIIa.T23_9_Sub.measurable_ztsum
