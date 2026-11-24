import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.PsipTermReg

/-!
# `PartIII-b:C/asrc/ra/5/6` : joint `C³` regularity of `ψ^p_A` (target `psipAC3`)

Source 4963-4981, 4978.  Closes the target `psipAC3` by applying the reduction `psipAC3_of`
(in `PartIII-b_C_asrc_ra_5_4`) to the `j = 0` term regularity `psipTermReg`
(in `PartIII-b_C_asrc_ra_5_4/PsipTermReg`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Joint `C³` regularity of `ψ^p_A`** on `s > 0` (source 4963-4981, 4978). -/
theorem psipAC3 (as : ℝ) (χf : ℝ → ℝ) : PsipAC3 as χf :=
  psipAC3_of as χf (psipTermReg as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
