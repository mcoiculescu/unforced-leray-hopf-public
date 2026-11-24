import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1.L4
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `SepFarDecay` assembled from its four leaves (`PartIII-b:IIIb-D2/3/1/3/1/1/1`)

Source `the November 2 reference manuscript` 4155-4186, 3604-3621, 3631-3646.
The conditional theorem `sepFarDecay_of` takes the kernel bounds `SepKernelBounds` and the four
leaves (`SepWZeroOfRoutZero`, `FarPointwise`, `FarMajorantBound`, `SepWFderivIntegral`), each
proved in `Sub/PartIII-b_IIIb-D2_3_1_3_1_1_1/L1..L4`; `IIIa.sepKernelBounds` is the unconditional
`sep:kernel` of `PartIII-a:T15`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepFarDecay : SepFarDecay :=
  sepFarDecay_of UnforcedLeray.Short.IIIa.sepKernelBounds sepWZeroOfRoutZero farPointwise
    farMajorantBound sepWFderivIntegral

end UnforcedLeray.Short.PartIIIb.Concrete

end
