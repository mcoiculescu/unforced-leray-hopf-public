import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_3_3
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.CylDeriv
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.CylCompOfDeriv

/-!
# Part III-b, task `PartIII-b:C/srcL/9/5/3/3` (`SCCylComp`): composition with `cylR`

`scCylComp : SCCylComp` from the homogeneous derivative bound `scCylDeriv`
(`Leaves/CylDeriv.lean`, task `PartIII-b:C/srcL/9/5/3/3/1`) and the Faà di Bruno step
`scCylCompOfDeriv` (`Leaves/CylCompOfDeriv.lean`, task `PartIII-b:C/srcL/9/5/3/3/2`), via
`scCylComp_of` (`Sub/PartIII-b_C_srcL_9_5_3_3.lean`).  Source: `the November 2 reference manuscript`
lines 4161-4166, 4178-4186.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem scCylComp : SCCylComp :=
  scCylComp_of scCylDeriv scCylCompOfDeriv

end UnforcedLeray.Short.PartIIIb.Concrete
