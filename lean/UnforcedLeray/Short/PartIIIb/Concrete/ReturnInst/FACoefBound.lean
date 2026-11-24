import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.Support
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.BmatBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.CellBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.ChartConv

/-!
# `faCoefBound`: `FACoefBound` from the five leaves of `PartIII-b:C/inst/9`

Source `the November 2 reference manuscript`:
`ret:general-affine-bounds` first line 5009-5016, proof 5063-5079, cutoff 4953-4963.

The proof instantiates `faCoefBound_of` with the leaves `fAcSupport`, `bmatBound`,
`fAcCellBound`, `fAcMeas` and `chartL2Conv`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem faCoefBound (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) : FACoefBound as χf :=
  faCoefBound_of as χf hχ (fAcSupport χf) (bmatBound as χf) fAcCellBound (fAcMeas as χf)
    chartL2Conv

end UnforcedLeray.Short.PartIIIb.Concrete
