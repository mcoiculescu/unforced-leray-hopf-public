import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2.L4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2.L5

/-!
# `PartIII-b:C/ward/13/8/2`: `BgPresGradClosure` proved

Source `the November 2 reference manuscript`
117-118, 2641-2642. The statement `BgPresGradClosure` is from `Sub/PartIII-b_C_ward_13_8.lean`;
the composition `bgPresGradClosure_proved_of` is from `Sub/PartIII-b_C_ward_13_8_2.lean`; the cutoff
family `cutoffFamily` is from `L1.lean`, the Deny-Lions constant `denyLionsConst` from `L4.lean`, and
`gradL2Closure_of_cutoff` from `L5.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bgPresGradClosure_proved : BgPresGradClosure :=
  bgPresGradClosure_proved_of (gradL2Closure_of_cutoff cutoffFamily denyLionsConst)

end UnforcedLeray.Short.PartIIIb.Concrete
