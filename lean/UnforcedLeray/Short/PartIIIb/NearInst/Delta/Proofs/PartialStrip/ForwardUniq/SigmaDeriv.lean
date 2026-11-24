import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.Props

/-!
# `FUSigmaDeriv` (item `PartIII-b:C/near/delta/9/1/3`)

The derivative of the smooth transition `σ = Real.smoothTransition` is nonnegative (`σ` is
monotone), bounded (it is continuous and vanishes off `[0,1]`), and vanishes on `(-∞,0) ∪ (1,∞)`
(`σ` is locally constant there).  Source 3541-3545 (cutoffs on `[δ_j, B]`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem fuSigmaDeriv : UnforcedLeray.Short.PartIIIb.NearInst.Delta.FUSigmaDeriv := by
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hcont : Continuous (deriv Real.smoothTransition) := hsm.continuous_deriv (by norm_num)
  have hzero : ∀ x : ℝ, (x < 0 ∨ 1 < x) → deriv Real.smoothTransition x = 0 := by
    intro x hx
    rcases hx with hx | hx
    · have hev : Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hx] with y hy
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
      rw [hev.deriv_eq]
      simp
    · have hev : Real.smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
      rw [hev.deriv_eq]
      simp
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x => ?_⟩
  have hnn : 0 ≤ deriv Real.smoothTransition x := Real.smoothTransition.monotone.deriv_nonneg
  have hup : deriv Real.smoothTransition x ≤ max C 1 := by
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · have hb := hC x hx
      rw [Real.norm_eq_abs] at hb
      exact le_trans (le_trans (le_abs_self _) hb) (le_max_left _ _)
    · have hx' : x < 0 ∨ 1 < x := by
        simp only [mem_Icc, not_and_or, not_le] at hx
        exact hx
      rw [hzero x hx']
      exact le_trans zero_le_one (le_max_right _ _)
  exact ⟨hnn, hup, fun h => hzero x h⟩

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
