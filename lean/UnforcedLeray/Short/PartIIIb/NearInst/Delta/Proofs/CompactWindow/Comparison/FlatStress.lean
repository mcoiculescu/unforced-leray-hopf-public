import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2_3
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.PlanarReferenceExists
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.CellPtChangeAll
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.FlatStressReal
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.FlatStressFree
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.FreeStressUnique

/-!
# Flat stress transport (item `PartIII-b:C/near/delta/8/2/3`)

Assembles `flatStressTransport` from the five lemmas of `FlatStress/`, via
`flatStressTransport_of` (source of record `the November 2 reference manuscript`,
1678-1690, 3427-3440, 3956-3967).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem flatStressTransport : FlatStressTransport :=
  flatStressTransport_of planarReferenceExists cellPtChangeAll flatStressReal flatStressFree
    freeStressUnique

end UnforcedLeray.Short.PartIIIb.NearInst.Delta

end
