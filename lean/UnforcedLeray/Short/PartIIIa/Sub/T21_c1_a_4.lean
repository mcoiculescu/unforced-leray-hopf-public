import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4.Of
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4.Ext
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4.Sectors
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4.EllSelf

/-!
# `PartIII-a:T21/c1/a/4`: `SeedBiorth` from the three leaves

Source: `the November 2 reference manuscript`
lines 603-610.  Assembles `seedBiorth_of` (in `Of.lean`) with the leaf proofs
`seedBiorthExt_proof` (`Ext.lean`), `seedSectors_proof` (`Sectors.lean`) and
`seedEllSelf_proof` (`EllSelf.lean`).
-/

set_option autoImplicit false

theorem seedBiorth_proof : UnforcedLeray.Short.IIIa.SeedBiorth :=
  UnforcedLeray.Short.IIIa.seedBiorth_of
    seedBiorthExt_proof
    seedSectors_proof
    seedEllSelf_proof
