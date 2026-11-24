import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_2
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.NvEquivar
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.GradEquivar
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.GradToEquivar

/-!
# `PartII-b:T10/7/1/1/2`: `gl_rotInv` (`GLRotInv`)

Source of record: `the November 2 reference manuscript` lines 1912-1921.
The three equivariance inputs `gl_nvEquivar`, `gl_gradEquivar`, `gl_gradToEquivar` are proved
in `GLRot/`; the decomposition `gl_rotInv_of` is in `Sub/PartII-b_T10_7_1_1_2`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem gl_rotInv : UnforcedLeray.Short.IIb.GLRotInv :=
  gl_rotInv_of gl_nvEquivar gl_gradEquivar gl_gradToEquivar

end UnforcedLeray.Short.IIb
