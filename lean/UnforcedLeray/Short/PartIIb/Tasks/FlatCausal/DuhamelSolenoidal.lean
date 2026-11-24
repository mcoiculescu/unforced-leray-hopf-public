import UnforcedLeray.Short.PartIIb.Sub.T12_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.Integrable
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.Swap
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.SliceAll
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.SliceGauss
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.GaussExtend
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.HeatAdjoint
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.HeatSmooth
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.HeatDecay

/-!
# Part II-b, task `PartII-b:T12/6`: solenoidality of the Duhamel integrand

Source of record: `the November 2 reference manuscript`, line 1924 (the heat flow
preserves solenoidality, `P_0 G = G`). Target: `DuhamelSolenoidal`, assembled from the eight
leaves of `Tasks/FlatCausal/DuhamelSolenoidal/` by `duhamelSolenoidal_of` (`Sub/T12_6.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- Solenoidality of the Duhamel integrand: the eight leaf predicates assembled by `duhamelSolenoidal_of`. -/
theorem duhamelSolenoidal : UnforcedLeray.Short.IIb.DuhamelSolenoidal :=
  duhamelSolenoidal_of dsolIntegrable dsolSwap dsolSliceAll dsolSliceGauss dsolGaussExtend
    dsolHeatAdjoint dsolHeatSmooth dsolHeatDecay

end UnforcedLeray.Short.IIb
