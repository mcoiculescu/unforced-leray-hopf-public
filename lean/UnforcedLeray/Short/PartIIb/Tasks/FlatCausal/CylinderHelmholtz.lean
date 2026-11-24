import UnforcedLeray.Short.PartIIb.Sub.T12_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzExists

/-!
# Part II-b, task `PartII-b:T12/1` (`CylinderHelmholtzLr`), assembled form

Source: `the November 2 reference manuscript` lines 1670, 1923-1926, 1930.
The two leaves are `cylHelmholtzExists` (`HelmholtzExists.lean`, task T12/1/6) and
`cylHelmholtzUnique` (`HelmholtzUnique.lean`, task T12/1/3). They are combined by
`cylinderHelmholtzLr_of` from `Sub/T12_1.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cylinderHelmholtzLr : UnforcedLeray.Short.IIb.CylinderHelmholtzLr :=
  cylinderHelmholtzLr_of cylHelmholtzExists cylHelmholtzUnique

end UnforcedLeray.Short.IIb
