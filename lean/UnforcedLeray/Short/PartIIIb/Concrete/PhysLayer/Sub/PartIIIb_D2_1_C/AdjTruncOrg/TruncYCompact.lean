import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg

/-!
# `truncYCompact`: the truncated field `Φₙ = curl(χₙ ψ)` has `y`-compact support

Source: `the November 2 reference manuscript` lines 1334-1337, 1351-1362,
1470-1480.  For `‖y‖ > 2(n+1)` one has `χₙ(y) = 0` (`cutχ_eq_zero`) and `∇χₙ(y) = 0`
(the support clause of `CutBounds`), so `truncPhi n D = χₙΦ + ∇χₙ × ψ` vanishes there.
Take `R = 2(n+1) + 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The cross product with a zero left factor vanishes. -/
theorem crossC_zero_left_trunc (b : CVec3) : crossC 0 b = 0 := by
  unfold crossC
  ext i
  fin_cases i <;> simp

theorem truncYCompact : TruncYCompact := by
  unfold TruncYCompact
  intro hCut n D
  obtain ⟨C, _, hall⟩ := hCut
  refine ⟨2 * ((n : ℝ) + 1) + 1, fun τ y hy => ?_⟩
  have hy3 : 2 * ((n : ℝ) + 1) < ‖y‖ := by linarith
  obtain ⟨hg, -⟩ := (hall n y).1 (Or.inr hy3)
  have hc : cutχ n y = 0 := cutχ_eq_zero n hy3.le
  unfold truncPhi
  simp only [hc, hg, zero_smul, zero_add, crossC_zero_left_trunc]
