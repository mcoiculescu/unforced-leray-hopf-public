import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_3

/-!
# Part II-b, task `PartII-b:T10/7/1/1/3/6` (`GLBuildPieces/ChartPeriodic`): q-periodicity of the chart profile

Source of record: `the November 2 reference manuscript` lines 1912-1921 (chart 1639-1668).

Target: `gl_chartPeriodic : UnforcedLeray.Short.IIb.GLChartPeriodic`.

Proof outline. Pointwise in `x = (s, q, η)`: the shift `q ↦ q + c` does not change `s`, so the
indicator `0 < s` agrees on both sides. For `s ≤ 0` both sides are `0`. For `s > 0`,
`invChart ε (s, q + c, η) = (τ + 2εc, ϱ, z)` where `(τ, ϱ, z) = invChart ε (s, q, η)`, and the
`2εc`-periodicity of `A, B` in `τ` gives equality.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem gl_chartPeriodic : UnforcedLeray.Short.IIb.GLChartPeriodic := by
  unfold GLChartPeriodic
  intro c ε A B hA hB
  unfold QPeriodic
  refine Filter.Eventually.of_forall (fun x => ?_)
  rcases x with ⟨s, q, η⟩
  by_cases hs : 0 < s
  · have hinv : invChart ε (s, (q + c, η)) =
        ((invChart ε (s, (q, η))).1 + 2 * ε * c, (invChart ε (s, (q, η))).2) := by
      refine Prod.ext ?_ rfl
      simp only [invChart]
      ring
    show (Real.sqrt s : ℂ) • chartProf ε A B (s, (q + c, η)) =
      (Real.sqrt s : ℂ) • chartProf ε A B (s, (q, η))
    unfold chartProf
    simp only [hs, ite_true, hinv, hA, hB]
  · show (Real.sqrt s : ℂ) • chartProf ε A B (s, (q + c, η)) =
      (Real.sqrt s : ℂ) • chartProf ε A B (s, (q, η))
    unfold chartProf
    simp only [hs, ite_false]

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gl_chartPeriodic
