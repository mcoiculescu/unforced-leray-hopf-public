import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint

/-!
# `PartII-b:T10/org/3`: `AdjSolSolenoidal`

Source `the November 2 reference manuscript` lines 1359-1361, 1426-1440, 1498-1500.
The statement is `adjSolSolenoidal_of` applied to the adjoint at `r = 2` (`PartII-a:F09`), the
Leray-commutation lemma (`PartII-b:T10/org/3/2`) and the fixed-point lemma (`PartII-b:T10/org/3/1`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem adjSolSolenoidal : UnforcedLeray.Short.IIb.AdjSolSolenoidal :=
  adjSolSolenoidal_of UnforcedLeray.Short.PartIIa.commonBodyAdjoint adjointLerayCommute
    ysigmaFixedByLeray

end UnforcedLeray.Short.IIb
