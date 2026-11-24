import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L5

/-!
# `sepWSmoothOn_of` (`PartIII-b:IIIb-D2/3/1/1/2`)

Source of record: `the November 2 reference manuscript` 3604-3621
(`sep:kernel`, `sep:resolvent`). The five leaf hypotheses of `sepWSmoothOn_of_of` are discharged
by the leaf theorems `paramContDiff`, `heatLerayKSmooth`, `sepPhiMeasurable`,
`sepGapPointwise`, `sepGapMajorantIntegrable`; only the kernel bound `hK` remains a hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepWSmoothOn_of (hK : IIIa.SepKernelBounds) : SepWSmoothOn :=
  sepWSmoothOn_of_of hK paramContDiff heatLerayKSmooth sepPhiMeasurable sepGapPointwise
    sepGapMajorantIntegrable

end UnforcedLeray.Short.PartIIIb.Concrete
