import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.HpAC2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.PsiC1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.FECont

/-!
# `PartIII-b:C/asrc/ra/8/5` : `RPerMeas` from the three proved regularity leaves

Source of record: `the November 2 reference manuscript` 5023-5028, 4978.

Applies `rPerMeas_of` (in `PartIII-b_C_asrc_ra_8_5`) to the leaves `hpAC2` (`HpAC2`),
`affPsiC1` (`AffPsiC1`) and `affFECont` (`AffFECont`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`RPerMeas`** (source 5023-5028, 4978): `s·r_per` is a.e. strongly measurable for the source
measure, from the joint regularity of `h^p_A`, `Ψ_A` and `f_A + e_A`. -/
theorem rPerMeas (as : ℝ) (χf : ℝ → ℝ) : RPerMeas as χf :=
  rPerMeas_of as χf (hpAC2 as χf) (affPsiC1 as χf) (affFECont as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
