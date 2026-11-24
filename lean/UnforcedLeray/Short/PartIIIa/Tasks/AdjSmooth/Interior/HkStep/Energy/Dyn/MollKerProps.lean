import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Normed.Group.Basic

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem mollKerProps : UnforcedLeray.Short.IIIa.MollKerProps := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · exact (molBump n).contDiff_normed
  · exact (molBump n).hasCompactSupport_normed
  · intro y hy
    unfold molKer
    by_contra hne
    have hmem : y ∈ Function.support ((molBump n).normed volume) := hne
    rw [(molBump n).support_normed_eq] at hmem
    rw [Metric.mem_ball, dist_zero_right] at hmem
    have hrOut : (molBump n).rOut ≤ 1 := by
      show 1 / ((n : ℝ) + 1) ≤ 1
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [div_le_one (by positivity)]
      linarith
    linarith

end UnforcedLeray.Short.IIIa
