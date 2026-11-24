import UnforcedLeray.Short.PartI.Sub.PartI_T04_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.MildConcatSeedRestart
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.MildConcatDuhamelSplit

/-!
# Part I, task `PartI:T04/1`: `MildConcat`

Source: `the November 2 reference manuscript` lines 270-277.

`mildConcat` is `mildConcat_of` (`Sub/PartI_T04_1.lean`) applied to the two leaves:
the seed restart identity `concatSeedRestart` (`MildConcatSeedRestart.lean`, task `PartI:T04/1/1`)
and the Duhamel split `concatDuhamelSplit` (`MildConcatDuhamelSplit.lean`, task `PartI:T04/1/2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Concatenation of compact mild solutions** (`MildConcat`, lines 270-277): the assembly of
`mildConcat_of` from the seed restart and the Duhamel split. -/
theorem mildConcat : MildConcat :=
  mildConcat_of concatSeedRestart concatDuhamelSplit

end UnforcedLeray.Short.PartI
