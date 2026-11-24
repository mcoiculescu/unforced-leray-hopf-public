import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.RingLiftBddOfR07
import UnforcedLeray.Short.PartIIa.Tasks.R07BoundedDerivs

/-!
# `RingLiftBdd` assembly (task `PartIII-b:C/ward/12/3/1/2/6/1/3/1`)

Source `the November 2 reference manuscript`
lines 1217-1219 and 1322-1325.

Combines `ringLiftBdd_of_ringBoundedDerivs` with `UnforcedLeray.Short.PartIIa.ringBoundedDerivs`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`RingLiftBdd`** (source lines 1217-1219, 1322-1325): smooth extension of the ring velocity
lift across the symmetry axis with uniform spatial derivative bounds up to order `2` for `R ≥ 2`. -/
theorem ringLiftBdd : RingLiftBdd :=
  ringLiftBdd_of_ringBoundedDerivs UnforcedLeray.Short.PartIIa.ringBoundedDerivs

#print axioms ringLiftBdd

end UnforcedLeray.Short.PartIIIb.Concrete
