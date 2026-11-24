import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4.Vanish
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4.Cont
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4.Norm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.Cell
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.PsiC1

/-!
# `PartIII-b:C/asrc/ra/9/4/Bound` : `GradRemBound` from the four leaves and `AffPsiC1`

Source of record: `the November 2 reference manuscript`, lines 5039-5043,
5063-5079, 4978, 5024.  Composes `gradRemBound_of` with `gradRemVanish`, `gradRemCont`,
`gradRemNorm`, `psiKCellL2` and `affPsiC1`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`GradRemBound` for the explicit remainder** (source 5039-5043, 5063-5079). -/
theorem gradRemBound (as : ℝ) (chi : ℝ → ℝ) : GradRemBound as chi :=
  gradRemBound_of as chi (gradRemVanish as chi) (gradRemCont as chi) (gradRemNorm as chi)
    (psiKCellL2 as chi) (affPsiC1 as chi)

end UnforcedLeray.Short.PartIIIb.Concrete
