import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_8
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WeakGlue.Decomp
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WeakGlue.Consistency
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WeakGlue.MeasGlue

/-!
# Leaf `PartII-b:T13/1/8`: weak derivatives are local (SP 1928-1933)

Assembles the three leaves `WglDecomp` (finite window decomposition of a test), `WglConsistency`
(consistency of local weak derivatives on overlaps) and `WglMeasGlue` (measurable periodic gluing)
into `WeakGlue` via `weakGlue_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem weakGlue : UnforcedLeray.Short.IIb.WeakGlue :=
  weakGlue_of wglDecomp wglConsistency wglMeasGlue

end UnforcedLeray.Short.IIb
