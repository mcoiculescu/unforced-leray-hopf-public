import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound.Support
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.BmatBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound.AyBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound.CellBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound.L2Conv

/-!
# `PartIII-b:C/inst/10`: `EACoefBound` assembled from the six leaves

Source `the November 2 reference manuscript` 5009-5016 (`E_A` bound) and
5063-5079 (the residual `e_A` has size `C M(A)(s^{3/2}+s^{5/2})`).

`eaCoefBound_of` (`Sub/PartIII-b_C_inst_10.lean`) takes the six leaf statements as
hypotheses; this file discharges them with the leaf theorems:
`eaCSupport` (Support), `bmatBound` (BmatBound), `ayBound` (AyBound), `eaCCellBound`
(CellBound), `eaCMeas` (Meas), `chartL2Conv` (L2Conv).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem eaCoefBound (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) : EACoefBound as χf :=
  eaCoefBound_of as χf hχ (eaCSupport χf) (bmatBound as χf) (ayBound as χf) eaCCellBound
    (eaCMeas as χf) chartL2Conv

end UnforcedLeray.Short.PartIIIb.Concrete
