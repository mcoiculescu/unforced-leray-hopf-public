import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_3_1_5_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakDiv.CylMollSwapDiv.Int1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakDiv.CylMollSwapDiv.Int2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakDiv.CylMollSwapDiv.MollComp

/-!


Source: `the November 2 reference manuscript` lines 1670, 1923-1926.
The decomposition `cylMollSwapDiv_of` (Sub file) reduces `CylMollSwapDiv` to the three leaves
`cylSwapInt1`, `cylSwapInt2` and `cylMollComp`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cylMollSwapDiv : UnforcedLeray.Short.IIb.CylMollSwapDiv :=
  cylMollSwapDiv_of CylSwapInt1Proof.cylSwapInt1 CylSwapInt2Proof.cylSwapInt2 cylMollComp

end UnforcedLeray.Short.IIb
