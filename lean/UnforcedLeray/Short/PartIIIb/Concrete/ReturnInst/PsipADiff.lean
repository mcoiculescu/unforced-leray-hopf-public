import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.XPart
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.SPart

/-!
# `PartIII-b:C/inst/5`: `PsipADiff` from the x-part and the s-part

Source `the November 2 reference manuscript` lines 4973-4980 and 4741-4745.
The x-part `psiPhiXDiff` (`PsipADiff/XPart.lean`) and the s-part `psipASDiff`
(`PsipADiff/SPart.lean`) are plugged into the compiled reduction `psipADiff_of`
(`Sub/PartIII-b_C_inst_5.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `PsipADiff` (source 4973-4980, 4741-4745): the x-part and the s-part, combined. -/
theorem psipADiff (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) : PsipADiff as χf :=
  psipADiff_of as χf hχ psiPhiXDiff (psipASDiff as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
