import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.PsiSubst
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.ParamInt7
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.PsiFSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.PsiFMeas
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.PsiFDom

/-!
# Proof of `SCPsiSmooth` (source 4178-4186, 4917-4937)

Assembles the five leaf proofs (`scPsiSubst`, `scParamInt7`, `scPsiF_smooth`, `scPsiF_meas`,
`scPsiF_dom`) through the decomposition lemma `scPsiSmooth_of`.
Source: `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem scPsiSmooth : SCPsiSmooth :=
  scPsiSmooth_of scPsiSubst scParamInt7 scPsiF_smooth scPsiF_meas scPsiF_dom

end UnforcedLeray.Short.PartIIIb.Concrete
