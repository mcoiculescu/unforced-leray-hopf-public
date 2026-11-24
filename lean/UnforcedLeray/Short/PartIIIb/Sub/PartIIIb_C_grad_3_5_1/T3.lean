import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1_3.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1_3.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1_3.L3

/-!
# `PartIII-b:C/grad/3/5/1/3` task T3: `HpALocUnif` from the three pieces

Source `the November 2 reference manuscript`
4991, 5063-5079.  Assembles `hpALocUnif` from `hpAGaussUnif` (L1, uniform Gaussian majorant),
`hpACompact` (L2, compact regions) and `hpAJointBound` (L3, joint value and derivative bound)
via `hpALocUnif_of`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hpALocUnif (as : ℝ) : HpALocUnif as :=
  hpALocUnif_of as hpAGaussUnif hpACompact (hpAJointBound as)

end UnforcedLeray.Short.PartIIIb.Concrete
