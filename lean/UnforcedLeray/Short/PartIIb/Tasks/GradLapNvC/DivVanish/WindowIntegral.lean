import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_4_2
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivVanish.LocInt
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivVanish.WindowIntegral.WinPerFacts
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivVanish.WindowIntegral.GDivPeriodicRep
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivVanish.WindowIntegral.WinFinite
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivVanish.WindowIntegral.RingBridgeC
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivVanish.WindowIntegral.WinIntCell

/-!
# Part II-b, task `PartII-b:T09/4/2` (`ChartWindowIntegral`): assembly

Source of record: `the November 2 reference manuscript`, lines 1639-1668, 1912-1916.

The glue `chartWindowIntegral_of` (in `Sub/PartII-b_T09_4_2.lean`) takes the leaves
`WinPerFacts`, `GDivPeriodicRep`, `DivLocInt`, `WinFinite`, `RingBridgeC`, `WinIntCell`;
each is proved by its own leaf file.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem chartWindowIntegral_proof : UnforcedLeray.Short.IIb.ChartWindowIntegral :=
  chartWindowIntegral_of winPerFacts gDivPeriodicRep divLocInt_proof winFinite ringBridgeC
    winIntCell

end UnforcedLeray.Short.IIb
