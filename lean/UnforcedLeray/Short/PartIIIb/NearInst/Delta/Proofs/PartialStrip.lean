import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_9
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.MaskedStripBound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.MaskedSupport
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressKernelRealization
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StripKernelBound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.BoxDenseZ
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ZeroEntranceCausal
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.GainStripRatio

/-!
# `partialStripBlock_of` (item `PartIII-b:C/near/delta/9`)

Source of record `the November 2 reference manuscript`, 3996-4009.
Assembly of `partialStripBlock_of_props` (Sub file `PartIII-b_C_near_delta_9`) from
`maskedStripBound_of`, `maskedSupport_of`, `zeroEntranceCausal_of` and `gainStripRatio`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem partialStripBlock_of (hK : UnforcedLeray.Short.IIIa.SepKernelBounds)
    (hY : UnforcedLeray.Short.IIIa.SepYoung)
    (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique) : PartialStripBlock :=
  partialStripBlock_of_props
    (UnforcedLeray.Short.PartIIIb.NearInst.Masked.maskedStripBound_of
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.stressKernelRealization
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.stripKernelBound_of hK hY)
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.boxDenseZ)
    (UnforcedLeray.Short.PartIIIb.NearInst.Masked.maskedSupport_of
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.stressKernelRealization
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.boxDenseZ)
    (zeroEntranceCausal_of hU)
    gainStripRatio

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
