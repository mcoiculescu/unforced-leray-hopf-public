import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.WindowCutoff
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.GammaBound
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.NormTransport

/-!
# Compact window comparison (item `PartIII-b:C/near/delta/8/2`)

Assembles `compactWindowComparison` from the four lemmas of `Comparison/`, via
`compactWindowComparison_of` (source of record `the November 2 reference manuscript`,
1692-1722, 3956-3967).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem compactWindowComparison (hC : UnforcedLeray.Short.PartIIa.NearCompactFreeComparison) (hS : UnforcedLeray.Short.PartIIa.NearStressMapExists) (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique) : CompactWindowComparison :=
  compactWindowComparison_of windowCutoffExists gammaWindowBound flatStressTransport windowNormTransport hC hS hU

end UnforcedLeray.Short.PartIIIb.NearInst.Delta

end
