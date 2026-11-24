import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarKernelL2.farOutMajorant
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarKernelL2.farMajL2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarKernelL2.farOutMeasurable

/-!


Assembles the three leaves `farOutMajorant`, `farMajL2` and `farOutMeasurable` through the
decomposition `farKernelL2_of_parts` (compiled in `Sub/PartIIIb_C_near_masked_14`), which is
stated there under the name `farKernelL2_of_parts` so that it does not clash with this theorem.
Source: `the November 2 reference manuscript` (3996-4011, 3604-3621, 2683).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem farKernelL2_of (hK : UnforcedLeray.Short.IIIa.SepKernelBounds) : FarKernelL2 :=
  UnforcedLeray.Short.PartIIIb.NearInst.Masked.farKernelL2_of_parts
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.farOutMajorant
    _root_.farMajL2
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.farOutMeasurable
    hK

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
