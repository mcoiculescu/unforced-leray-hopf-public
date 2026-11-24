import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.FarMaskVanish
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.GainBlockRatio

/-!
# Proof of `compactWindowBlock_of` (item `PartIII-b:C/near/delta/8`)

Source of record: `the November 2 reference manuscript`, paragraph 3956-3994.
Assembles `CompactWindowBlock` from `farMaskVanish`, `compactWindowComparison`, and
`gainBlockRatio` via `UnforcedLeray.Short.PartIIIb.NearInst.Delta.compactWindowBlock_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta.Target

theorem compactWindowBlock_of (hC : UnforcedLeray.Short.PartIIa.NearCompactFreeComparison) (hS : UnforcedLeray.Short.PartIIa.NearStressMapExists) (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique) : CompactWindowBlock :=
  UnforcedLeray.Short.PartIIIb.NearInst.Delta.compactWindowBlock_of
    farMaskVanish (compactWindowComparison hC hS hU) gainBlockRatio

end UnforcedLeray.Short.PartIIIb.NearInst.Delta.Target
