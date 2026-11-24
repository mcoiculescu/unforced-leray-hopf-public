import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4_2.TailIterated
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4_2.GaussHeat
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4_2.TailPartDt
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4_2.TailLapPart

/-!
# `KernelPartialHeat` (unconditional)

Source `the November 2 reference manuscript`
3600-3610. The four tail/Gaussian facts are proved in the `_2` folder; this file applies
`KPH.kernelPartialHeat_of` to them.
-/

theorem kernelPartialHeat : UnforcedLeray.Short.PartIIIb.Concrete.KernelPartialHeat :=
  UnforcedLeray.Short.PartIIIb.Concrete.KPH.kernelPartialHeat_of
    UnforcedLeray.Short.PartIIIb.Concrete.KPH.tailIterated
    UnforcedLeray.Short.PartIIIb.Concrete.KPH.gaussHeat
    UnforcedLeray.Short.PartIIIb.Concrete.KPH.tailPartDt
    UnforcedLeray.Short.PartIIIb.Concrete.KPH.tailLapPart
