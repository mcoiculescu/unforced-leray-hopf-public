import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.FTermReg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.ETermReg

/-!
# `PartIII-b:C/asrc/ra/5/4` : joint regularity of the `f_A`, `e_A` sums (target `affFECont`)

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
Closes the target `affFECont` by applying the reduction `affFECont_of` (in
`PartIII-b_C_asrc_ra_5_4`) to the two term-level regularity results `fTermReg` and `eTermReg`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Joint regularity of the `f_A`, `e_A` sums** on `s > 0` (source 4963-4981, 4978). -/
theorem affFECont (as : ℝ) (χf : ℝ → ℝ) : AffFECont as χf :=
  affFECont_of as χf (fTermReg as χf) (eTermReg as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
