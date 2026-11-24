import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2

/-!
# Lemma 1: a mollifier sequence exists (`ContDiffBump`, normalized by its integral)

Source of record: `the November 2 reference manuscript`, line 2531 (spatial
mollification). The radii are `rIn = 1/(2(n+1))`, `rOut = 1/(n+1)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The bump of radii `1/(2(n+1)) < 1/(n+1)` centred at `0`. -/
def mollBump (n : ℕ) : ContDiffBump (0 : UnforcedLeray.Space) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    apply one_div_lt_one_div_of_lt
    · positivity
    · linarith

theorem mollSeqExists : MollSeqExists := by
  refine ⟨fun n => (mollBump n).normed volume, fun n => ?_⟩
  refine ⟨(mollBump n).contDiff_normed, (mollBump n).hasCompactSupport_normed (μ := volume),
    (mollBump n).nonneg_normed, (mollBump n).integral_normed (μ := volume), ?_⟩
  rw [(mollBump n).tsupport_normed_eq (μ := volume)]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
