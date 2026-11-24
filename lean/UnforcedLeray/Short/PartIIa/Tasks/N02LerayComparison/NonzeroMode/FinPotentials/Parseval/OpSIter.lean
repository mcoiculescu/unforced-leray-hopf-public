import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4_7
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Parseval.PdS

/-!

Source: `the November 2 reference manuscript`, lines 1713-1727, 1744-1745.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- `opS^[α]` of a finite mode sum is the mode sum of `nzS2^[α]`, for `α ∈ {0,1}`. -/
theorem nzFpOpSIter : UnforcedLeray.Short.PartIIa.NzFpOpSIter := by
  unfold NzFpOpSIter
  intro c M g hg α hα p
  have hα2 : α < 2 := Finset.mem_range.mp hα
  interval_cases α
  · simp only [Function.iterate_zero, id_eq, nzModeSum]
  · simp only [Function.iterate_one]
    rw [nzfpOpSModeSum c M g hg p]
    simp only [smul_eq_mul]

end UnforcedLeray.Short.PartIIa
