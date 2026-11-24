import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3_2_4_13

/-!
# Bridge from the cell heat integral to the `ℝ³` heat average (task
`PartIII-b:C/near/pins/3/4/2/3/2/4/13/3`)

Proves `ODHT_Bridge`: for `z = (x, τ)` in the cell, `heatConv (ιx P) s (cellFn g) z` is the
`ℝ³` heat average `Heat.average s (g(τ, ·)) x`.  Route: unfold `heatConv` and `average`,
`ιx = inl` and `toCell (z - ιx y) = ((toCell z).1 - y, (toCell z).2)`, and
`Gaussian.gaussKernel_three_eq`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem odhtBridge : ODHT_Bridge := by
  intro P _ g s z
  have hc : ∀ y : UnforcedLeray.Gaussian.Euc 3,
      UnforcedLeray.B0223.toCell P (z - UnforcedLeray.B0223.ιx P y)
        = ((UnforcedLeray.B0223.toCell P z).1 - y, (UnforcedLeray.B0223.toCell P z).2) := by
    intro y
    simp [UnforcedLeray.B0223.toCell, UnforcedLeray.B0223.ιx]
  unfold UnforcedLeray.Heat.heatConv UnforcedLeray.Heat.average
  congr 1
  funext y
  rw [UnforcedLeray.Gaussian.gaussKernel_three_eq]
  simp only [cellFn, hc]

end UnforcedLeray.Short.PartIIIb.NearInst
