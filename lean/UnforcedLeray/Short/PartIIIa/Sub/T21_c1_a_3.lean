import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_3_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_3_2

/-!
# Part III-a, `PartIII-a:T21/c1/a/3`: the dual kernel of the Gaussian seed

Source: `the November 2 reference manuscript`, lines 601-610 and 2891-2897.
Assembles `SeedDualKernel` from `seedDualKernel_of` (in `T21_c1_a_3_of.lean`) with
`seedProfileOrderTwo_proof` (task /3/1) and `seedPolarPlane_proof` (task /3/2).
-/

set_option autoImplicit false

theorem seedDualKernel_proof : UnforcedLeray.Short.IIIa.SeedDualKernel :=
  UnforcedLeray.Short.IIIa.seedDualKernel_of
    seedProfileOrderTwo_proof
    seedPolarPlane_proof
