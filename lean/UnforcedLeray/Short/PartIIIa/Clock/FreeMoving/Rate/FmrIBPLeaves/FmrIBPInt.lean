import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5_1.Growth

/-!
# `PartIII-a:T21/c2/2/5/1`: integrability leaf of `FmrIBP` (SP 2950-2954)

`FmrIBPInt` from `fmrIBPInt_of` and the growth bound `mwGrowth` of the dilated weight.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem fmrIBPInt : FmrIBPInt := fmrIBPInt_of mwGrowth

end UnforcedLeray.Short.IIIa
