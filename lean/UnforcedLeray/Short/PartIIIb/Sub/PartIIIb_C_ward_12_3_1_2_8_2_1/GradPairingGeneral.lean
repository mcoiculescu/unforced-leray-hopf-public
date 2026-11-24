import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_4.GPSlice
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_4.GPCutoffLimit

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1/4`: `gradPairingGeneral` (assembly)

Source `the November 2 reference manuscript`
lines 1393-1400, 1409-1412.  Proves `GradPairingGeneral` (`ProjCommuteProps.lean`) from the
slice test `gpSlice` (`GPSlice.lean`, Lemma A) and the cutoff limit `gpCutoffLimit`
(`GPCutoffLimit.lean`, Lemma B), via `gradPairingGeneral_of` (`PartIII-b_C_ward_12_3_1_2_8_2_1_1_4.lean`).
-/

set_option autoImplicit false

noncomputable section

theorem gradPairingGeneral : UnforcedLeray.Short.PartIIIb.Concrete.GradPairingGeneral :=
  UnforcedLeray.Short.PartIIIb.Concrete.gradPairingGeneral_of
    UnforcedLeray.Short.PartIIIb.Concrete.gpSlice
    UnforcedLeray.Short.PartIIIb.Concrete.gpCutoffLimit
