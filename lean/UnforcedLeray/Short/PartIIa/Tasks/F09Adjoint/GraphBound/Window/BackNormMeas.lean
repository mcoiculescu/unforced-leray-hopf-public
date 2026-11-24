import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1_4
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.AdjChart

/-!
# Part II-a, task `PartII-a:F09/3/1/4/1`: measurability of the reversed window component

Proves `AdjCompAEMeas` of `Sub/«PartII-a_F09_3_1_4»`, the analogue of `wd_aemeasurable`.
Source of record: `the November 2 reference manuscript`,
lines 1431-1441 (reversed chart `θ = 1 - e^{-t}`, `x = e^{-t/2} y`, with `t = τ₀ - τ`).

`adjComp ν τ₀ g` is the composition of `g` with the reversed chart `adjChart_qmp` applied to the
measure-preserving shift-and-flip `z ↦ (τ₀ - z.1, z.2)`, multiplied by a continuous weight and
cut off by the measurable set `{|z.1 - τ₀| < 1}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Parabolic

/-- The map `z ↦ (τ₀ - z.1, z.2)` is measure preserving on `ℝ × Space`. -/
theorem adjc_shift_mp (τ₀ : ℝ) :
    MeasurePreserving (fun z : ℝ × Space => (τ₀ - z.1, z.2)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (Measure.measurePreserving_sub_left volume τ₀).prod (MeasurePreserving.id volume)

/-- The composed reversed chart `z ↦ Φ(τ₀ - z.1, z.2)` is quasi measure preserving. -/
theorem adjc_comp_qmp (τ₀ : ℝ) :
    Measure.QuasiMeasurePreserving
      (fun z : ℝ × Space =>
        ((1 - Real.exp (-(τ₀ - z.1)), Real.exp (-(τ₀ - z.1) / 2) • z.2) : PS 3))
      volume volume := by
  have h := adjChart_qmp.comp (adjc_shift_mp τ₀).quasiMeasurePreserving
  have hf : ((fun p : ℝ × Space =>
        ((1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) : PS 3)) ∘
      (fun z : ℝ × Space => (τ₀ - z.1, z.2))) =
      (fun z : ℝ × Space =>
        ((1 - Real.exp (-(τ₀ - z.1)), Real.exp (-(τ₀ - z.1) / 2) • z.2) : PS 3)) := by
    funext z
    simp only [Function.comp_apply, neg_div]
  rw [hf] at h
  exact h

/-- **`PartII-a:F09/3/1/4/1`: measurability of the reversed window component.** -/
theorem adjCompAEMeas : AdjCompAEMeas := by
  intro ν τ₀ g hg
  have hgc : AEStronglyMeasurable (fun z : ℝ × Space =>
      g ((1 - Real.exp (-(τ₀ - z.1)), Real.exp (-(τ₀ - z.1) / 2) • z.2) : PS 3)) volume :=
    hg.comp_quasiMeasurePreserving (adjc_comp_qmp τ₀)
  have hexp : Measurable (fun z : ℝ × Space => ((Real.exp (-(τ₀ - z.1)) : ℝ) : ℂ)) := by
    fun_prop
  have hF : AEMeasurable (fun z : ℝ × Space =>
      (ν : ℂ) * ((Real.exp (-(τ₀ - z.1)) : ℝ) : ℂ) *
        g ((1 - Real.exp (-(τ₀ - z.1)), Real.exp (-(τ₀ - z.1) / 2) • z.2) : PS 3)) volume :=
    ((measurable_const.mul hexp).aemeasurable).mul hgc.aemeasurable
  have hS : MeasurableSet {z : ℝ × Space | |z.1 - τ₀| < 1} :=
    measurableSet_lt (by fun_prop) measurable_const
  have heq : adjComp ν τ₀ g = {z : ℝ × Space | |z.1 - τ₀| < 1}.indicator
      (fun z : ℝ × Space =>
        (ν : ℂ) * ((Real.exp (-(τ₀ - z.1)) : ℝ) : ℂ) *
          g ((1 - Real.exp (-(τ₀ - z.1)), Real.exp (-(τ₀ - z.1) / 2) • z.2) : PS 3)) := by
    funext z
    by_cases h : |z.1 - τ₀| < 1
    · simp [adjComp, h]
    · simp [adjComp, h]
  rw [heq]
  exact hF.indicator hS

end UnforcedLeray.Short.PartIIa
