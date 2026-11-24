import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.PairCLM
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.TestDeriv

/-!
# `outerGen` (task `PartIII-b:C/near/pins/3/4/2/3`)

Source `the November 2 reference manuscript` lines 1339-1362, 3346-3352, 4139-4146.
Assembly of the two leaves `outerPairCLM` (task `.../3/4/2/3/1`) and `outerTestDeriv`
(task `.../3/4/2/3/2`) through `outerGen_of` from `Sub/PartIII-b_C_near_pins_3_4_2_3.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem outerGen : OuterGen :=
  outerGen_of outerPairCLM outerTestDeriv

end UnforcedLeray.Short.PartIIIb.NearInst
