import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.Admissible
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.Eq
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.HeatIdentity
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.RemainderLimit
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.MainLimit

/-!
# Part II-b, leaf `PartII-b:T11/2/2` (`DualFTestZero`): composition of the five leaves.

Source: `the November 2 reference manuscript` 1923-1927.
`dualFTestZero_of` (`Sub/PartIIb_T11_2_2.lean`) applied to the leaf theorems
`DualTestAdmissible_proof` (`/1`), `DualTestEq_proof` (`/2`), `DualHeatIdentity_proof` (`/3`),
`DualRemainderLimit_proof` (`/4`) and `DualMainLimit_proof` (`/5`).
-/

set_option autoImplicit false

noncomputable section

theorem dualFTestZero_proof : UnforcedLeray.Short.IIb.DualFTestZero :=
  UnforcedLeray.Short.IIb.dualFTestZero_of
    DualTestAdmissible_proof
    UnforcedLeray.Short.IIb.DualTestEq_proof
    UnforcedLeray.Short.IIb.DualHeatIdentity_proof
    DualRemainderLimit_proof
    UnforcedLeray.Short.IIb.DualMainLimit_proof
