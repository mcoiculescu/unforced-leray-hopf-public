import UnforcedLeray.Short.PartIIb.Sub.T12_6_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.DuhamelIntegrable.Meas
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.DuhamelIntegrable.BoxSlice

/-!
# Part II-b, task `PartII-b:T12/6/2` (`DsolDuhamelIntegrable`): assembly

Source of record: `the November 2 reference manuscript`, lines 1920-1930.
The conditional reduction `dsolDuhamelIntegrable_of` is in `Sub/T12_6_2.lean`; its two
hypotheses are discharged by `dsolDMeas` (leaf `PartII-b:T12/6/2/1`) and `boxSlice`
(leaf `PartII-b:T12/6/2/5`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem dsolDuhamelIntegrable : UnforcedLeray.Short.IIb.DsolDuhamelIntegrable :=
  dsolDuhamelIntegrable_of dsolDMeas boxSlice

end UnforcedLeray.Short.IIb
