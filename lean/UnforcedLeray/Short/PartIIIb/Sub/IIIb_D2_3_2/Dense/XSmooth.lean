import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Defs
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.A
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.C
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.D

/-!
# `WardXrSmoothData` (`PartIII-b:IIIb-D2/3/2/11/2`, source 4161-4186, 3604-3621)

Composes `wardXrSmoothData_of` with the seven proved source-fact lemmas of
`Sub/IIIb-D2_3_2_11_2/` (A, B1, B2, B3, B4, C, D).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem wardXrSmoothData_proved : WardXrSmoothData :=
  wardXrSmoothData_of smoothOldSource_proved wardX0SmoothInf_proved wardX0DecayInf_proved
    wardX0DivFree_proved outPrimSmoothInf_proved wardXrSmoothOfParts_proved wardXrAxiOfX0_proved

end UnforcedLeray.Short.PartIIIb.Concrete
