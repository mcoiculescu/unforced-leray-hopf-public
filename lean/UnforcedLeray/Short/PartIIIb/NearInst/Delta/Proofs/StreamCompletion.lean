import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_5_1
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.StreamMeanCompletion
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.StreamFluctCompletion
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.RaisedStreamSplit

/-!
# `PartIII-b:C/near/delta/5/1`: `streamCompletionDecay` (source 2703-2729)

Source `the November 2 reference manuscript`
lines 2703-2729: combines `streamMeanCompletion`, `streamFluctCompletion`, and `raisedStreamSplit`
via `streamCompletionDecay_of` to establish `StreamCompletionDecay`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

/-- **Target (`PartIII-b:C/near/delta/5/1`)**: weighted bound for the stream completion
(`StreamCompletionDecay`, source lines 2703-2729). -/
theorem streamCompletionDecay : UnforcedLeray.Short.PartIIIb.NearInst.Delta.StreamCompletionDecay :=
  streamCompletionDecay_of streamMeanCompletion streamFluctCompletion raisedStreamSplit

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
