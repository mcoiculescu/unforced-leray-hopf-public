import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_2
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWZ
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ

/-!
# `PartII-b:T10/7/1/2` (`GradWeakOfLift`)

Source of record: `the November 2 reference manuscript` lines 1912-1921, 1639-1668.
Combines `gwZ` (`GWZ`) and `gwQ` (`GWQ`) via `gradWeakOfLift_of`.
-/

set_option autoImplicit false

open UnforcedLeray.Short.IIb

theorem gradWeakOfLift : UnforcedLeray.Short.IIb.GradWeakOfLift :=
  gradWeakOfLift_of gwZ gwQ

#print axioms gradWeakOfLift
