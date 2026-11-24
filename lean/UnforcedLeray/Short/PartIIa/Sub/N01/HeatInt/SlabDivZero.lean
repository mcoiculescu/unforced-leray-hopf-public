import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_1
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.SlabDivZero.SlabWeak

/-!
# `PartII-a:N01/9/1/2/4/1` (decomposition): `SlabDivZero`

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383, 3426-3430.  The proposition `SlabDivZero` (defined in
`PartII-a_N01_9_1_2_4.lean`) follows from `slabDivZero_of` (in `PartII-a_N01_9_1_2_4_1.lean`)
and `slabWeakToClassical` (in `SlabDivZero/SlabWeak.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

theorem slabDivZero : UnforcedLeray.Short.PartIIa.N01.SlabDivZero :=
  slabDivZero_of slabWeakToClassical

end UnforcedLeray.Short.PartIIa.N01
