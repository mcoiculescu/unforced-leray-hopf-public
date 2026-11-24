import UnforcedLeray.Short.PartIIIa.Clock.Moving
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble
import UnforcedLeray.Short.PartIIIa.Clock.AmplGronwall
import UnforcedLeray.Short.PartIIIa.Clock.FrameAssemble

/-!
# Part III-a, task `PartIII-a:T21/longfull`: unconditional `LongForwardEstimate`

Source: `the November 2 reference manuscript`.
Assembles `longForwardEstimate_of` (`Clock/LongAssemble.lean`, `T21/long`) with
`goodFrameExists` (`Clock/FrameAssemble.lean`, `T21/frame`) and
`amplitudeGronwall` (`Clock/AmplGronwall.lean`, `T21/c4`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem longForwardEstimate : UnforcedLeray.Short.IIIa.LongForwardEstimate := by
  exact longForwardEstimate_of goodFrameExists amplitudeGronwall

end UnforcedLeray.Short.IIIa
