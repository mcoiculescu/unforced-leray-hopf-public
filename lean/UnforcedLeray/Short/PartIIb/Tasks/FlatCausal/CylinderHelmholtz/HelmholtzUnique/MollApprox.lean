import UnforcedLeray.Short.PartIIb.Sub.T12_1_3_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylLocInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollSmoothPeriodic
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollBounded
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollMemLp
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakDiv
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakSol

/-!
# Part II-b, task `PartII-b:T12/1/3/1` (`CylMollApprox`), unconditional form

Source: `the November 2 reference manuscript` lines 1670, 1923-1926.
The six leaves `a`-`f` (local integrability, smooth periodicity, boundedness, `L^r` membership,
weak divergence-free identity, weak solenoidal orthogonality) are proved in the `MollApprox/`
folder and assembled by `cylMollApprox_of` from `Sub/T12_1_3_1.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cylMollApprox : UnforcedLeray.Short.IIb.CylMollApprox :=
  cylMollApprox_of cylLocInt cylMollSmoothPeriodic cylMollBounded cylMollMemLp
    cylMollWeakDiv cylMollWeakSol

end UnforcedLeray.Short.IIb
