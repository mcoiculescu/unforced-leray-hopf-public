import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_3_1_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakDiv.TestMollIsTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakDiv.TestMollDeriv
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakDiv.CylMollSwapDiv

/-!


Source: `the November 2 reference manuscript` lines 1670, 1923-1926.
The decomposition `cylMollWeakDiv_of` (Sub file) reduces `CylMollWeakDiv` to the three leaves
`testMollIsTest`, `testMollDeriv` and `cylMollSwapDiv`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cylMollWeakDiv : UnforcedLeray.Short.IIb.CylMollWeakDiv :=
  cylMollWeakDiv_of testMollIsTest testMollDeriv cylMollSwapDiv

end UnforcedLeray.Short.IIb
