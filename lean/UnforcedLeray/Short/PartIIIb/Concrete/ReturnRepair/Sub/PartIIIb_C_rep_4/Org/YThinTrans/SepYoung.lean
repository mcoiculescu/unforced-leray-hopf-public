import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1.Rep

/-!
# `PartIII-b:C/rep/4/2/org/1`: `SepYoungThin`

One-line application of `sepYoungThin_of` (`Sub/PartIII-b_C_rep_4_2_org_1.lean`) to
`sepWeakRepresentationThin` (`Sub/PartIII-b_C_rep_4_2_org_1/Rep.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepYoungThin (dm dp : ℝ) : SepYoungThin dm dp :=
  sepYoungThin_of dm dp (sepWeakRepresentationThin dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
