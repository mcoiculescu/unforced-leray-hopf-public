import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.Core

/-!
# `PartIII-b:C/asrc/ra/9/4/org/4` : the cell `L²` bound `PsiKCellL2` from `PsiADerivCell`

Source of record `the November 2 reference manuscript`
lines 5063-5079, 4978, 5024.  Composes `psiKCellL2_of` with the Gaussian lattice-sum core `psiADerivCell`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Cell `L²` bound for `(𝒦+2)Ψ_A`** (source 5063-5079, 4978, 5024). -/
theorem psiKCellL2 (as : ℝ) (χf : ℝ → ℝ) : PsiKCellL2 as χf :=
  psiKCellL2_of as χf (psiADerivCell as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
