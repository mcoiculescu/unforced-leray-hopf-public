import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_5
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.SDLine
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.SDEuler
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.SDMat

/-!
# Part III-b, task `PartIII-b:C/srcL/9/5/5` (`SCSDeriv`): receiver jets

`scSDeriv : SCSDeriv` from the three leaves `sdLine` (`Leaves/SDLine.lean`, `PartIII-b:C/srcL/9/5/5/1`),
`sdEuler` (`Leaves/SDEuler.lean`, `PartIII-b:C/srcL/9/5/5/2`) and `sdMat`
(`Leaves/SDMat.lean`, `PartIII-b:C/srcL/9/5/5/3`), via `scSDeriv_of`
(`Sub/PartIII-b_C_srcL_9_5_5.lean`).  Source: `the November 2 reference manuscript`
lines 4178-4186, 4917-4937.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem scSDeriv : SCSDeriv :=
  scSDeriv_of sdLine sdEuler sdMat

end UnforcedLeray.Short.PartIIIb.Concrete
