import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5

/-!
# `PartIII-b:C/rep/2/5`: the axis `{ϱ = 0}` is null (`WGXAxisNull`)

The axis is contained in the proper submodule `{y | y 0 = 0}` of `ℝ³`, which has Haar measure zero.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The plane `{y₀ = 0}` as a submodule of `ℝ³`. -/
def axisPlane : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) where
  carrier := {y | y 0 = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, PiLp.add_apply] at *
    rw [ha, hb]; ring
  zero_mem' := by
    simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, PiLp.smul_apply, smul_eq_mul] at *
    rw [ha]; ring

theorem axisPlane_ne_top : axisPlane ≠ ⊤ := by
  intro h
  have hmem : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : EuclideanSpace ℝ (Fin 3)) ∈ axisPlane := by
    rw [h]; exact Submodule.mem_top
  have h1 : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : EuclideanSpace ℝ (Fin 3)) 0 = 0 := hmem
  simp at h1

theorem wgxAxisNull : WGXAxisNull := by
  unfold WGXAxisNull
  apply MeasureTheory.measure_mono_null (t := (axisPlane : Set (EuclideanSpace ℝ (Fin 3))))
  · intro y hy
    have hy' : ϱ y = 0 := hy
    unfold ϱ at hy'
    have hsq : y 0 ^ 2 + y 1 ^ 2 ≤ 0 := (Real.sqrt_eq_zero'.mp hy')
    have h0sq : y 0 ^ 2 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have h0 : y 0 = 0 := (pow_eq_zero_iff (by norm_num)).mp h0sq
    show y 0 = 0
    exact h0
  · exact MeasureTheory.Measure.addHaar_submodule volume axisPlane axisPlane_ne_top

end UnforcedLeray.Short.PartIIIb.Concrete

end
