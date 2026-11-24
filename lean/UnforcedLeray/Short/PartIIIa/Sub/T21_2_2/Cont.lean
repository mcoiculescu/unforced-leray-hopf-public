import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.Cont.Age
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.Cont.F0
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.Cont.F1

/-!
# Part III-a, `PartIII-a:T21/2/2/1`: continuity of `E_0, E_1` assembled

Source of record: `the November 2 reference manuscript` lines 3060-3071.

Assembles `adjointEnergyCont_of` from the age map (`Cont/Age.lean`, `adjAgeMap`), the `E_0`
continuity (`Cont/F0.lean`, `adjF0Cont`) and the `E_1` continuity (`Cont/F1.lean`, `adjF1Cont`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem adjointEnergyCont (m : ℝ) (hm : 8 < m) : AdjointEnergyCont m :=
  adjointEnergyCont_of m adjAgeMap adjF0Cont adjF1Cont

end UnforcedLeray.Short.IIIa
