import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_5
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.StreamCompletion

/-!
# `PartIII-b:C/near/delta/5`: `rawStreamCompletion` (source 2724-2729)

Source `the November 2 reference manuscript`
lines 2724-2729: derives `RawStreamCompletion` from `streamCompletionDecay` via
`rawStreamCompletion_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

/-- **Target (`PartIII-b:C/near/delta/5`)**: weighted bound on the raw stream completion
(`RawStreamCompletion`, source lines 2724-2729). -/
theorem rawStreamCompletion : RawStreamCompletion :=
  rawStreamCompletion_of streamCompletionDecay

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
