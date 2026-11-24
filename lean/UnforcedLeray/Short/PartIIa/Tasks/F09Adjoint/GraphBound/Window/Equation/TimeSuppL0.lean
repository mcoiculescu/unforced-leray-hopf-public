import UnforcedLeray.Units.B0005.Bridge.Unfold
import UnforcedLeray.Units.B0411.Operators

/-!


`TimeSupp A B G` is preserved by `L₀ ν = T₀ - ν Δ - ½` (`B0411.L0`): every summand is a
spatial or phase derivative of `G` (or `G` itself), and each vanishes at `(τ, y)` when
`τ ∉ [A, B]`, since `G` is locally zero there.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open UnforcedLeray.PhaseTrace UnforcedLeray.PhaseSpace

namespace UnforcedLeray.Short.PartIIa

theorem timeSupp_L0 {G : ℝ × Space → CVec3} {A B : ℝ} (hG : TimeSupp A B G) (ν : ℝ) :
    TimeSupp A B (UnforcedLeray.B0411.L0 ν G) := by
  intro τ y hτ
  have hd : PhaseSpace.dτ G (τ, y) = 0 := UnforcedLeray.B0005.timeSupp_fderiv_apply hG (1, 0) τ y hτ
  have hr : PhaseSpace.radialT G (τ, y) = 0 := by
    simp only [PhaseSpace.radialT]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [UnforcedLeray.B0005.timeSupp_dy hG j τ y hτ, smul_zero]
  have hl : PhaseSpace.lapT G (τ, y) = 0 := UnforcedLeray.B0005.timeSupp_lapT hG τ y hτ
  simp only [UnforcedLeray.B0411.L0, UnforcedLeray.B0411.T0]
  rw [hd, hr, hl, hG τ y hτ]
  simp

end UnforcedLeray.Short.PartIIa
