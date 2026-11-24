import UnforcedLeray.Short.PartI.Sub.L_T02_1_4_6_4_5_2

/-!
# Part I, task `PartI:T02/1/4/6/4/5/2/2`: uniform sup bound of the representative

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `AdvLipSupW`.  Immediate from `IsSpatialRepOn.bounded` (`HasBoundedDerivsOn T w`) at
derivative order zero, since `norm_iteratedFDeriv_zero` identifies the order-zero norm with
`‖w s z‖`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

theorem advLipSupW_proof : UnforcedLeray.Short.PartI.AdvLipSupW := by
  intro ν c T hν hc hc1 hT u hu w hw
  obtain ⟨M, hM⟩ := hw.bounded 0
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro r hr z
  have h := hM r hr z
  rw [norm_iteratedFDeriv_zero] at h
  exact h.trans (le_max_left _ _)

end UnforcedLeray.Short.PartI
