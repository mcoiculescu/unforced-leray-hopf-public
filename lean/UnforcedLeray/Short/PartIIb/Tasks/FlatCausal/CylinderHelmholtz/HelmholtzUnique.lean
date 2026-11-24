import UnforcedLeray.Short.PartIIb.Sub.T12_1_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.SmoothPointwise

/-!
# Part II-b, task `PartII-b:T12/1/3` (`CylHelmholtzUnique`), assembled form

Source: `the November 2 reference manuscript` lines 1670, 1923-1926.
The two leaves are proved in the `HelmholtzUnique/` folder: `cylMollApprox` (`MollApprox.lean`)
and `cylSmoothWeakToPointwise` (`SmoothPointwise.lean`). They are combined by
`cylHelmholtzUnique_of` from `Sub/T12_1_3.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cylHelmholtzUnique : UnforcedLeray.Short.IIb.CylHelmholtzUnique :=
  cylHelmholtzUnique_of cylMollApprox cylSmoothWeakToPointwise

end UnforcedLeray.Short.IIb
