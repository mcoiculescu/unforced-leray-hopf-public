import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_3
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.CylRSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.Chi1D
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.CylComp

/-!
# Part III-b, task `PartIII-b:C/srcL/9/5/3` (`SCChiJet`): the cutoff jet bound

`scChiJet χy : SCChiJet χy` from the three leaves `scCylRSmooth` (`Leaves/CylRSmooth.lean`),
`scChi1D χy` (`Leaves/Chi1D.lean`) and `scCylComp` (`Leaves/CylComp.lean`), via `scChiJet_of`
(`Sub/PartIII-b_C_srcL_9_5_3.lean`).  Source: `the November 2 reference manuscript`
lines 4161-4166, 4178-4186.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem scChiJet (χy : ℝ → ℝ) : SCChiJet χy :=
  scChiJet_of scCylRSmooth (scChi1D χy) scCylComp

end UnforcedLeray.Short.PartIIIb.Concrete
