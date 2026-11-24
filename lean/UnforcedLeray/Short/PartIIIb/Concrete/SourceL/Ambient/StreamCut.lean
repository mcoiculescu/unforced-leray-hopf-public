import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.PsiSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.PsiBound
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.ChiJet
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.XJet
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.SDeriv

/-!
# Part III-b, task `PartIII-b:C/srcL/9/5` (`streamCutJet`): assembly

`streamCutJet χy : StreamCutJet χy`, assembled from the leaves
`scPsiSmooth`, `scPsiBound`, `scChiJet χy` (through `scXJet_of_parts`) and `scSDeriv`,
via `streamCutJet_of`.  Source: `the November 2 reference manuscript`
lines 4178-4186, 4917-4937.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem streamCutJet (χy : ℝ → ℝ) : StreamCutJet χy :=
  streamCutJet_of (scXJet_of_parts χy scPsiSmooth scPsiBound (scChiJet χy)) scSDeriv

end UnforcedLeray.Short.PartIIIb.Concrete
