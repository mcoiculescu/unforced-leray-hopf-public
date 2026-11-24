import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.Core
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.RingLiftBdd

/-!
# `rawDerivBdd` (task `PartIII-b:C/ward/12/3/1/2/6/1/3`)

Source `the November 2 reference manuscript`
lines 1217-1219 and 1322-1325.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rawDerivBdd : RawDerivBdd :=
  rawDerivBdd_of ringLiftBdd

#print axioms rawDerivBdd

end UnforcedLeray.Short.PartIIIb.Concrete
