import UnforcedLeray.Short.PartIIb.Sub.T11_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.LocInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.DuBoisReymond

/-!
# Part II-b, leaf `PartII-b:T11/2` (`FlatDualConstancy`), composition of the three leaves.

Source: `the November 2 reference manuscript` 1923-1927.
`flatDualConstancy_of` (`Sub/T11_2.lean`) applied to `flatEqCellStream` (`T11/1`),
`dualFLocInt_proof` (`T11/2/1`), `dualFTestZero_proof` (`T11/2/2`) and `duBoisReymond_proof`
(`T11/2/3`).
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Short.IIb in
theorem flatDualConstancy : UnforcedLeray.Short.IIb.FlatDualConstancy :=
  flatDualConstancy_of flatEqCellStream dualFLocInt_proof dualFTestZero_proof duBoisReymond_proof

#print axioms flatDualConstancy
