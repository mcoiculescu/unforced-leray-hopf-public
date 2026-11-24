import UnforcedLeray.Short.PartIIb.Sub.T12_1_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.LerayOfRiesz

/-!
# Part II-b, task `PartII-b:T12/1/1` (`PlaneHelmholtzLr`): the unconditional planar Leray bound

Source: `the November 2 reference manuscript` lines 1670 and 1923-1926
(planar Calderon-Zygmund Leray projection `P_0 = I - grad Delta^-1 div` on `R^2`, Grafakos
Cor. 5.2.8).

This file assembles the two leaves
* `planeRieszFamilyExists : PlaneRieszFamilyExists` (`PartII-b:T12/1/1/2`, `RieszFamily.lean`),
* `planeLerayOfRiesz : PlaneLerayOfRiesz` (`PartII-b:T12/1/1/3`, `LerayOfRiesz.lean`),
through the conditional theorem `planeHelmholtzLr_of_riesz` of `Sub/T12_1_1.lean`.
-/

namespace UnforcedLeray.Short.IIb

/-- **Leaf assembly `PartII-b:T12/1/1`**: the planar Helmholtz/Leray bound in `L^2 cap L^r`,
unconditionally, from the planar Riesz family and the Riesz-to-Leray step. -/
theorem planeHelmholtzLr : UnforcedLeray.Short.IIb.PlaneHelmholtzLr :=
  planeHelmholtzLr_of_riesz planeRieszFamilyExists planeLerayOfRiesz

end UnforcedLeray.Short.IIb
