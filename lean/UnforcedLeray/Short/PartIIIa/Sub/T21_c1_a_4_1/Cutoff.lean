import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4_1

/-!
# `PartIII-a:T21/c1/a/4/1`: the cutoff leaf `ExtCutoff`

Source: `the November 2 reference manuscript`
lines 603-610. A Mathlib `ContDiffBump` on `ℂ` with `rIn = 1`, `rOut = 2`.
-/

set_option autoImplicit false

theorem extCutoff_proof : UnforcedLeray.Short.IIIa.ExtCutoff := by
  let b : ContDiffBump (0 : ℂ) :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  refine ⟨fun z => b z, ?_, ?_, ?_, ?_⟩
  · exact b.contDiff
  · exact b.hasCompactSupport
  · intro z
    exact ⟨b.nonneg, b.le_one⟩
  · intro z hz
    apply b.one_of_mem_closedBall
    show z ∈ Metric.closedBall (0 : ℂ) 1
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hz
