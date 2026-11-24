import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_15
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_15.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_15.L2

/-!
# `PartIII-b:C/near/masked/15`: `farKernelLinear`

The far kernel is linear on box tensors (`FarKernelLinear`, source 3905-3912), obtained from the
two source leaves `maskedLiftSource` (L1) and `maskedLiftMoment` (L2) through `farKernelLinear_of`
of the Sub file.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem farKernelLinear : FarKernelLinear :=
  farKernelLinear_of maskedLiftSource maskedLiftMoment

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
