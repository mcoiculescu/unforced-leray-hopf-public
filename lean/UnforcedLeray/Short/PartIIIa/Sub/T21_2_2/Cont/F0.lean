import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_1_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.Cont.F0_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.Cont.F0_2

/-!
# Part III-a, `PartIII-a:T21/2/2/1/2`: `AdjF0Cont` assembled from its two leaves

Source of record: `the November 2 reference manuscript` (SP), lines 2854-2865 and
3060-3071. `adjF0Cont_of` (`PartIII-a_T21_2_2_1_2.lean`) reduces `AdjF0Cont` to the change of
variables `AdjF0Ident` (leaf `F0_1`) and the continuity `AdjF0Core` (leaf `F0_2`).
-/

namespace UnforcedLeray.Short.IIIa

theorem adjF0Cont : UnforcedLeray.Short.IIIa.AdjF0Cont :=
  adjF0Cont_of adjF0Ident_proof adjF0Core_proof

end UnforcedLeray.Short.IIIa
