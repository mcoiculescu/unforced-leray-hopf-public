import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_3_1_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakSol.SolTestMollIsSolTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakSol.CylMollSwapSol

/-!


Source: `the November 2 reference manuscript` lines 1670, 1923-1926.
Composes `cylMollWeakSol_of` (in `Sub/PartIIb_T12_1_3_1_6.lean`) with the leaves
`solTestMollIsSolTest` (`T12/1/3/1/6/1`) and `cylMollSwapSol` (`T12/1/3/1/6/2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cylMollWeakSol : UnforcedLeray.Short.IIb.CylMollWeakSol :=
  cylMollWeakSol_of solTestMollIsSolTest cylMollSwapSol

end UnforcedLeray.Short.IIb
