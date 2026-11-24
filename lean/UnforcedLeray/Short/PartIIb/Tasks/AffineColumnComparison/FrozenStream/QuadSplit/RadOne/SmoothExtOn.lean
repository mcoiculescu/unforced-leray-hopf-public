import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_2_4_1

/-!
# Part II-b, task `PartII-b:G4/2/2/4/1/3`: `SmoothExtOn`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: cutoff `χ(t) = smoothTransition(4t - 1)` (zero for `t ≤ 1/4`, one for `t ≥ 1/2`) and
`h' = χ · h`. On `(0,∞)` this is a product of smooth functions; on `(-∞,1/4)` it vanishes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

theorem smoothExtOn : UnforcedLeray.Short.IIb.SmoothExtOn := by
  intro h hh
  have hchi : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (4 * t - 1)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have hC : ContDiff ℝ ∞ (fun t : ℝ => ((Real.smoothTransition (4 * t - 1) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hchi
  refine ⟨fun t => ((Real.smoothTransition (4 * t - 1) : ℝ) : ℂ) * h t, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : 0 < x
    · exact hC.contDiffAt.mul (hh.contDiffAt (Ioi_mem_nhds hx))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds (show x < 1 / 4 by push_neg at hx; linarith)] with s hs
      have hs' : s < 1 / 4 := hs
      rw [Real.smoothTransition.zero_of_nonpos (show 4 * s - 1 ≤ 0 by linarith),
        Complex.ofReal_zero, zero_mul]
  · intro t ht
    beta_reduce
    rw [Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 4 * t - 1 by linarith)]
    simp

end
