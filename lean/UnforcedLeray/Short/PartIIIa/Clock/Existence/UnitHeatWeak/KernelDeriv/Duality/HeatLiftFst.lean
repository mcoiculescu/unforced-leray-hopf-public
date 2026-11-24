import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_1_2_1

/-!
# Part III-a, `PartIII-a:T21/3/2/1/2/1`: first component of the heat lift

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
The first component of `heat τ (z ↦ (F z, 0))` is the real heat convolution `∫ G(w) F(z - w)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.IIIa.Exist

theorem heatLiftFst : UnforcedLeray.Short.IIIa.Exist.HeatLiftFst := by
  intro τ hτ F z
  rw [UnforcedLeray.B0284.heat_apply_of_pos hτ]
  by_cases h : Integrable (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 τ w * F (z - w))
  · have hpair : Integrable (fun w : ℝ × ℝ =>
        ((UnforcedLeray.B0284.heatKernel2 τ w * F (z - w), (0 : ℝ)) : ℝ × ℝ)) :=
      h.prodMk (integrable_zero _ _ _)
    have key := (ContinuousLinearMap.fst ℝ ℝ ℝ).integral_comp_comm hpair
    simp only [ContinuousLinearMap.coe_fst'] at key
    simpa [Prod.smul_mk, smul_eq_mul] using key.symm
  · have hnot : ¬ Integrable (fun w : ℝ × ℝ =>
        UnforcedLeray.B0284.heatKernel2 τ w • ((fun z => (F z, (0 : ℝ))) (z - w) : ℝ × ℝ)) := by
      intro hint
      apply h
      have := hint.fst
      simpa [Prod.smul_mk, smul_eq_mul] using this
    rw [integral_undef h, integral_undef hnot]
    simp
end UnforcedLeray.Short.IIIa.Exist
