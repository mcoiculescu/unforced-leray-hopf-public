import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1_2_3

/-!
# Part II-b, leaf `PartII-b:T08/1/2/3` (`DriftIBP`)

Source: `the November 2 reference manuscript` 1912-1915.
Integration by parts for the drift transpose against phase tests; the proof is
`driftIBP_of_phase` in `Sub/PartIIb_T08_1_2_3.lean`.
-/

set_option autoImplicit false

noncomputable section

theorem driftIBP_proof : UnforcedLeray.Short.IIb.DriftIBP :=
  UnforcedLeray.Short.IIb.driftIBP_of_phase

#print axioms driftIBP_proof
