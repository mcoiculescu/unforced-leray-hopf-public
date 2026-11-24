import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.Defs
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# `MollifierFamilyExists`

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
`Defs.lean` was corrected from `ContDiff ℝ ⊤` (analytic in `ℕ∞ω`, making the statement false) to
`ContDiff ℝ ∞` (smooth).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem mollifierFamilyExists_holds : MollifierFamilyExists := by
  let f : ∀ n : ℕ, ContDiffBump (0 : Space) := fun n =>
    ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_div_iff₀ (by positivity) this]; nlinarith⟩
  refine ⟨fun n => (f n).normed volume, fun n => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (f n).contDiff_normed
  · exact (f n).hasCompactSupport_normed
  · exact fun z => (f n).nonneg_normed z
  · exact (f n).integral_normed
  · intro z hz
    have hz' : z ∈ Function.support ((f n).normed volume) := hz
    rw [(f n).support_normed_eq, mem_ball, dist_zero_right] at hz'
    exact hz'.le

end UnforcedLeray.Short.PartIIIb.Concrete
