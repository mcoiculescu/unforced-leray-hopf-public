import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4_1.Cutoff
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4_1.SectorBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4_1.WeightBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4_1.RightDCT
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4_1.LeftDCT

/-!
# `PartIII-a:T21/c1/a/4/1`: assembly of `SeedBiorthExt`

Source: `the November 2 reference manuscript`
lines 603-610. Applies `seedBiorthExt_of` to the five leaf proofs.
-/

set_option autoImplicit false

theorem seedBiorthExt_proof : UnforcedLeray.Short.IIIa.SeedBiorthExt :=
  UnforcedLeray.Short.IIIa.seedBiorthExt_of extCutoff_proof extSectorBound_proof
    extWeightBound_proof extRightDCT_proof extLeftDCT_proof
