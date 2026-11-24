import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.NearYoungOld.Of
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.NearYoungOld

/-!
# `NearYoungOldBox` from `nearYoungOld` (source 5303-5306, 3902-3920, 4163-4166)

`ftOld` is `chiOStr`, and `nearYoungOld` (masked support of the near operator on the far mask, proved
on all stresses, not only box tensors) is exactly `χ_y S_N χ_o = 0`; the box case is a special case.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem nearYoungOldBox (dm dp : ℝ) : NearYoungOldBox dm dp := by
  intro D hst
  filter_upwards [nearYoungOld dm dp D hst] with n hn z hz F _
  exact hn z hz F

end UnforcedLeray.Short.PartIIIb.Concrete
