import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4_1

/-!
# Leaf B1 (`OscCutoff`): a smooth cutoff from `ContDiffBump`

Source of record: `the November 2 reference manuscript`, line 1086 and lines
1134-1140 (local Sobolev/elliptic estimate). The Prop `OscCutoff` is proved exactly as stated in
`Short/Spine/Sub/SP_CAN4_4_1.lean`.

Construction: the Mathlib bump centred at `c = (a + b) / 2` with `rIn = (b - a) / 2 + δ / 2` and
`rOut = (b - a) / 2 + δ`, where `δ = min (a - a') (b' - b) > 0`.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Polynomial
open scoped ContDiff Topology InnerProductSpace

theorem oscCutoff_proof : UnforcedLeray.Short.Spine.OscCutoff := by
  intro a b a' b' haa' hab hbb'
  obtain ⟨δ, hδ, hδa, hδb⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ a - a' ∧ δ ≤ b' - b :=
    ⟨min (a - a') (b' - b), lt_min (by linarith) (by linarith),
      min_le_left _ _, min_le_right _ _⟩
  let f : ContDiffBump ((a + b) / 2) :=
    { rIn := (b - a) / 2 + δ / 2
      rOut := (b - a) / 2 + δ
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  have hrIn : f.rIn = (b - a) / 2 + δ / 2 := rfl
  have hrOut : f.rOut = (b - a) / 2 + δ := rfl
  refine ⟨fun r => f r, f.contDiff, ?_, ?_, ?_, ?_⟩
  · intro r hr
    show f r = 1
    apply f.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le, hrIn]
    constructor <;> linarith [hr.1, hr.2]
  · intro r hr
    show f r = 0
    apply f.zero_of_le_dist
    rw [hrOut, Real.dist_eq]
    have h1 : (b - a) / 2 + δ ≤ -(r - (a + b) / 2) := by linarith
    exact h1.trans (neg_le_abs _)
  · intro r hr
    show f r = 0
    apply f.zero_of_le_dist
    rw [hrOut, Real.dist_eq]
    have h1 : (b - a) / 2 + δ ≤ r - (a + b) / 2 := by linarith
    exact h1.trans (le_abs_self _)
  · intro r
    exact ⟨f.nonneg' r, f.le_one⟩
