import UnforcedLeray.Short.PartI.Sub.PartI_T08_6
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureOrth.Word
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureOrth.Zero

/-!


Source: `the November 2 reference manuscript`, line 346.
`jetPressureOrth_proof` is `jetPressureOrth_of` applied to the two leaves
`jetPressureOrthWord_proof` (`PressureOrth/Word.lean`, task `PartI:T08/6/1`) and
`jetPressureOrthZero_proof` (`PressureOrth/Zero.lean`, task `PartI:T08/6/2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem jetPressureOrth_proof : UnforcedLeray.Short.PartI.JetPressureOrth :=
  jetPressureOrth_of jetPressureOrthWord_proof jetPressureOrthZero_proof

end UnforcedLeray.Short.PartI
