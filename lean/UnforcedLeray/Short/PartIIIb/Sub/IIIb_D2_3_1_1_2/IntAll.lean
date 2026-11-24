import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.Int
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L5
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
`SepIntegrableOfSource` from the accepted leaves of `sepWSmoothOn_of`
(source 3604-3621, 3631-3646).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepIntegrableOfSource_all : SepIntegrableOfSource :=
  sepIntegrableOfSource_of IIIa.sepKernelBounds sepPhiMeasurable sepGapPointwise
    sepGapMajorantIntegrable

end UnforcedLeray.Short.PartIIIb.Concrete
