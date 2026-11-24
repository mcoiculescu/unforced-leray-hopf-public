import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.EtaDeriv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.SDeriv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.ValBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.EtaBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.SBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.EtaTsum
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.STsum
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.SliceCont

/-!
# `PartIII-b:C/asrc/ra/9/4/org/4/1` : assembly of `PsiADerivCell` from the eight leaves

Source of record: `the November 2 reference manuscript`
lines 5063-5079, 4978, 5024.  The eight leaf modules `…/1/1` … `…/1/8` supply the hypotheses of
`psiADerivCell_of` (proved in `Defs`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`PsiADerivCell` from the eight leaves** (source 5063-5079, 4978, 5024). -/
theorem psiADerivCell (as : ℝ) (χf : ℝ → ℝ) : PsiADerivCell as χf :=
  psiADerivCell_of as χf psiTEtaDeriv psiTSDeriv psiTValBound psiTEtaBound psiTSBound
    psiAEtaTsum psiASTsum psiASliceCont

end UnforcedLeray.Short.PartIIIb.Concrete
