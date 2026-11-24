import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1

/-!
# Existence of a spatial approximate identity

Source `the November 2 reference manuscript`
lines 2562-2564 (local Friedrichs argument in `y`).

The approximate identity is the normalised bump `ρ_n = bump_n / ∫ bump_n` with
`bump_n` a `ContDiffBump` at `0` with radii `1/(2(n+1)) < 1/(n+1)`, so that
`tsupport ρ_n = closedBall 0 (1/(n+1))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The unnormalised bump with inner radius `1/(2(n+1))` and outer radius `1/(n+1)`. -/
def approxBump (n : ℕ) : ContDiffBump (0 : UnforcedLeray.Space) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact one_div_lt_one_div_of_lt hn (by linarith)

/-- **Existence of a spatial approximate identity** (source 2562-2564). -/
theorem exists_approxId : ExistsApproxId := by
  refine ⟨fun n => (approxBump n).normed volume, fun n => ?_⟩
  refine ⟨(approxBump n).contDiff_normed, (approxBump n).hasCompactSupport_normed,
    fun y => (approxBump n).nonneg_normed y, (approxBump n).integral_normed, ?_⟩
  exact le_of_eq (approxBump n).tsupport_normed_eq

end UnforcedLeray.Short.PartIIIb.Concrete
