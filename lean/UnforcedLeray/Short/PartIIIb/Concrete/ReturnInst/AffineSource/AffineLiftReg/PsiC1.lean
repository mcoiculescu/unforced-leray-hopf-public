import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_3.PsiASum
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_3.GpsiAEq
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_3.PpsiAGrowth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.GaussMul

/-!
# `PartIII-b:C/asrc/ra/5/3/PsiC1` : joint `C¹` regularity of `s Ψ_A` on `s > 0`

Closes the target `affPsiC1` (source 5024, 5040-5043, 4978) by applying the reduction
`affPsiC1_of` (in `PartIII-b_C_asrc_ra_5_3`) to the four sub-results: the lattice-sum form
`psiASum_proof`, the Gaussian-factor identity `gpsiA_eq_proof`, the polynomial growth
`ppsiA_growth_proof`, and the Gaussian multiplier bound `gaussMulHbd_proof 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Joint `C¹` regularity of `s Ψ_A` on `s > 0`** (source 5024, 5040-5043, 4978). -/
theorem affPsiC1 (as : ℝ) (χf : ℝ → ℝ) : AffPsiC1 as χf :=
  affPsiC1_of as χf psiASum_proof gpsiA_eq_proof (ppsiA_growth_proof as χf) (gaussMulHbd_proof 1)

end UnforcedLeray.Short.PartIIIb.Concrete
