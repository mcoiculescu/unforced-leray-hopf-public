import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_1
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.CellPairing
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.KernelDeriv
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.PairingCont

/-!
# Part III-a, `PartIII-a:T21/3/2/1`: `UnitHeatS0Weak` from three lemmas

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Assembles the three lemmas `unitHeatCellPairing` (L1), `unitHeatKernelDeriv` (L2) and
`unitHeatPairingCont` (L3) into `unitHeatS0Weak` via `unitHeatS0Weak_of`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace UnforcedLeray.Short.IIIa.Exist

theorem unitHeatS0Weak : UnforcedLeray.Short.IIIa.Exist.UnitHeatS0Weak :=
  unitHeatS0Weak_of unitHeatCellPairing unitHeatKernelDeriv unitHeatPairingCont

end UnforcedLeray.Short.IIIa.Exist
