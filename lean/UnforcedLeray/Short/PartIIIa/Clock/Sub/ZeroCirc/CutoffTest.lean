import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCircLeaves

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem zcCutoffTest : ZCCutoffTest := by
  intro c n
  have hsob := B0285.cutT_test c n
  refine ⟨⟨hsob.smooth, fun x => rfl, hsob.bounded⟩, fun x => B0285.fderiv_cutT_zero n x, fun x => ?_⟩
  exact B0285.fderiv_cutT_one n x

end UnforcedLeray.Short.IIIa
