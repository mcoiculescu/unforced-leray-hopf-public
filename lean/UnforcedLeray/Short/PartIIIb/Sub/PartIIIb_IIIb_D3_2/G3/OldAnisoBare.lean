import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoBareOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoBare.CellAdd
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoBare.CanFlowVel
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoBare.PreparedCompare
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoBare.BandForward

/-!
# `PartIII-b:IIIb-D3/2/G3/1/4`: `bareColUnit_of`

Source of record: `the November 2 reference manuscript`, lines 3314–3343,
3392–3401, 4416–4457, 4509–4543, 4610–4612.

Assembles `G3.BareColUnit D` from `bareCellAdd`, `bareCanFlowVel`, `preparedDatumCompare_of D`,
and `bandForwardAtH_of D hL` via `bareColUnit_of_leaves`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

/-- **Assembly of `G3.BareColUnit D`** (source lines 3314–3343, 3392–3401, 4416–4457,
4509–4543, 4610–4612). -/
theorem bareColUnit_of (D : SeqData) (hM : UnforcedLeray.Short.IIIa.CTMellin)
    (hA : UnforcedLeray.Short.IIIa.CTAnisotropy)
    (hL : UnforcedLeray.Short.IIIa.FullClockLongForward)
    (hRem : G3.LaterOutputRem D) : G3.BareColUnit D :=
  bareColUnit_of_leaves D hM hA hL hRem bareCellAdd bareCanFlowVel
    (preparedDatumCompare_of D) (bandForwardAtH_of D hL)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3
