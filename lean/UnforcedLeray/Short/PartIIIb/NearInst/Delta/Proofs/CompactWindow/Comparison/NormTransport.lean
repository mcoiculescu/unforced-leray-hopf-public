import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2_4
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.WindowNorm.InRestrNormLeOne
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.WindowNorm.ZsumTransportNorm
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.WindowNorm.CplxZsumAE
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.WindowNorm.OutRestrBinTransport

/-!
# Window norm transport (item `PartIII-b:C/near/delta/8/2/4`)

Assembles `windowNormTransport` from the four lemmas of `WindowNorm/`, via
`windowNormTransport_of` (source of record `the November 2 reference manuscript`,
3956-3967 step (d)).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem windowNormTransport : WindowNormTransport :=
  windowNormTransport_of inRestrNormLeOne zsumTransportNorm cplxZsumAE outRestrBinTransport

end UnforcedLeray.Short.PartIIIb.NearInst.Delta

end
