import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11_4
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L4_1
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L4_2
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L4_3
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L4_4

/-!
# `PartIII-b:C/inst/11/4`: `HAcMeas`

Source `the November 2 reference manuscript`
4979-4980, 5063-5079.  Reduction `hAcMeas_of` (four continuity leaves) is in
`Sub/PartIII-b_C_inst_11_4.lean`; the four leaves are `Sub/Leaves11/L4_1.lean` to
`Sub/Leaves11/L4_4.lean`.  The final theorem is `hAcMeas` below.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `HAcMeas` from the four continuity leaves (source 4979-4980, 5063-5079). -/
theorem hAcMeas (as : ℝ) (χf : ℝ → ℝ) : HAcMeas as χf :=
  hAcMeas_of as χf (hpAContOn as χf) (psipAContOn as χf) (psipADxContOn as χf) (psipADsContOn as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
