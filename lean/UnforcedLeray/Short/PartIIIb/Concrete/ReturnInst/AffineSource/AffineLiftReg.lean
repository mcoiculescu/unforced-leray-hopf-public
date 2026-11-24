import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RADefs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.HpAC2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.PsipAC3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.HCoefC2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.PsiC1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.FECont
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.HCoefPer
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.FEPer

/-!
# `PartIII-b:C/asrc/ra/5` : `AffineLiftReg` (target `affineLiftReg`)

Source of record: `the November 2 reference manuscript` lines 4963-4991, 5076-5079.
Closes `AffineLiftReg` by applying the reduction `affineLiftReg_of` (in the Sub file
`PartIII-b_C_asrc_ra_5`) to the five leaf facts: `affHCoefC2_of_hp_psip` fed with `hpAC2` and
`psipAC3`, and the leaves `affPsiC1`, `affFECont`, `affHCoefPer`, `affFEPer`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Regularity of the affine lift** (source 4963-4991, 5076-5079): `ĥ_A` is `C²`, `sΨ_A` is
`C¹`, and `F_A + E_A` is continuous, for `A ∈ 𝒜`. -/
theorem affineLiftReg (as : ℝ) (χf : ℝ → ℝ) : AffineLiftReg as χf :=
  affineLiftReg_of as χf
    (affHCoefC2_of_hp_psip as χf (hpAC2 as χf) (psipAC3 as χf))
    (affPsiC1 as χf)
    (affFECont as χf)
    (affHCoefPer as χf)
    (affFEPer as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
