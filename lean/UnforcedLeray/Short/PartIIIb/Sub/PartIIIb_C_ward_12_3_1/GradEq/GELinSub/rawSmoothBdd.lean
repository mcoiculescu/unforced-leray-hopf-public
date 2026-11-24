import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Lemmas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawPeriodicAll
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawDerivBdd

/-!
# `rawSmoothBdd` (task `PartIII-b:C/ward/12/3/1/2/6/1`)

Source `the November 2 reference manuscript`
lines 1214-1219 and 1305-1325.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rawSmoothBdd : RawSmoothBdd :=
  rawSmoothBdd_of rawJointSmooth rawPeriodicAll rawDerivBdd

end UnforcedLeray.Short.PartIIIb.Concrete
