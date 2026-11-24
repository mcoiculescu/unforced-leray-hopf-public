import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.Lift

/-!
# `PartII-b:T10/6/3/1/1b`: `q`-periodicity of the periodization

Reindex the `ℤ`-sum by `k ↦ k + 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.ChartLift

theorem perPeriodic_proof : UnforcedLeray.Short.IIb.ChartLift.PerPeriodic := by
  intro c φ x
  have key : ∀ k : ℤ, φ (x.1, (x.2.1 + c + (k : ℝ) * c, x.2.2)) =
      φ (x.1, (x.2.1 + (((k + 1 : ℤ)) : ℝ) * c, x.2.2)) := by
    intro k
    rw [show x.2.1 + c + (k : ℝ) * c = x.2.1 + (((k + 1 : ℤ)) : ℝ) * c by push_cast; ring]
  dsimp only [perCoord, UnforcedLeray.Short.IIb.qShift]
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun k : ℤ => φ (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)))]
  exact tsum_congr fun k => key k

end UnforcedLeray.Short.IIb.ChartLift
