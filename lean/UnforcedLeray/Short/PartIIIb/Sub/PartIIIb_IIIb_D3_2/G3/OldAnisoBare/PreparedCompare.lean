import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2_G3_1_4_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoBare.PreparedCompare.SeedLinkEq
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoBare.PreparedCompare.PeriodizeXmc

/-!
# `PartIII-b:IIIb-D3/2/G3/1/4/3`: `preparedDatumCompare_of`

Source of record: `the November 2 reference manuscript`, lines 597–610, 625–627,
3127–3130, 4416–4426, 4445–4447.

Assembles `G3.PreparedDatumCompare D` from `seedLinkEqPlanarMode_of D` and `periodizePlanarModeXmc_of`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

/-- **Comparison at `t = 0` between `FI.pair.q true 0` and `IIIa.preparedDatum D.Pl ν`**
(source lines 597–610, 625–627, 3127–3130, 4416–4426, 4445–4447). -/
theorem preparedDatumCompare_of (D : SeqData) : G3.PreparedDatumCompare D :=
  preparedDatumCompare_of_leaves D (seedLinkEqPlanarMode_of D) periodizePlanarModeXmc_of

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3
