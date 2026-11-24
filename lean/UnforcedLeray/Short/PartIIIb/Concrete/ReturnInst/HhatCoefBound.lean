import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L1
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L2
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L3
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L4
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.ChartConv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AyDiffAt

/-!
# `PartIII-b:C/inst/11`: unconditional `HhatCoefBound`

Source `the November 2 reference manuscript`:
`ret:general-affine-bounds` first line 5009-5016 (for `ĥ_A`), proof 5063-5079.

Discharges the six hypotheses of `hhatCoefBound_of` with the leaves:
`hAcSupport` (inst/11/1), `ayDerivBound` (inst/11/2), `hAcCellBound` (inst/11/3),
`hAcMeas` (inst/11/4), `ayBound` (inst/11/5), `chartL2Conv` (inst/9/5), `ayDiffAt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hhatCoefBound (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) :
    HhatCoefBound as χf :=
  hhatCoefBound_of as χf hχ (hAcSupport χf) (ayBound as χf) (ayDerivBound as χf)
    hAcCellBound (hAcMeas as χf) chartL2Conv (ayDiffAt as χf hχ)

end UnforcedLeray.Short.PartIIIb.Concrete
