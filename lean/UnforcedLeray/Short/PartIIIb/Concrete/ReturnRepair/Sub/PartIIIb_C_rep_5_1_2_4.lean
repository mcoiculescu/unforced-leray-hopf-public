import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4.WardGainMarginFalse
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_1

/-!
# `PartIII-b:C/rep/5/1/2/4`: `WardLateBin` (late bins only)

Source `the November 2 reference manuscript` lines 5585-5605.
One-line application of `wardLateBin_of` (`Assembly.lean`) to `thinMassBound`
(`PartIII-b_C_rep_5_1_2_1`), `wardYBinMass` (`PartIII-b_C_rep_5_1_2_4_1`), `chiOThinRep`
(`_4_2`), `binNormToAge` (`_4_3`), `massGained` (`_4_4`), and `lateGainMarginG`
(`WardGainMarginFalse`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem wardLateBin (D : SeqData) {dm dp : ℝ} (h : D.RepairStanding dm dp) :
    D.WardLateBin :=
  wardLateBin_of D h (thinMassBound D.K.mZ h.mZ_gt) (wardYBinMass D) chiOThinRep binNormToAge
    (massGained D.K.mZ) (lateGainMarginG D h)

end UnforcedLeray.Short.PartIIIb.Concrete
