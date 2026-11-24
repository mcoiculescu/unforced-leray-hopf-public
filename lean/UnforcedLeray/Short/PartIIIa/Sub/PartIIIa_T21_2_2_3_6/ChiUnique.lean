import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.Unique
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K4
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K5

/-!
# `PartIII-a:T21/2/2/3/6/1`: `AdjChiUnique` from the five leaves

Assembles the compiled `adjChiUnique_of` with the five leaves K1 (`kernelBSExists`),
K2 (`weakFieldBandInt`), K3 (`CellUniqueAux.cellUnique`), K4 (`weakDerivC1`) and K5
(`bandMulTest`). Source: `the November 2 reference manuscript` lines 2875-2896,
3052-3058.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem adjChiUnique (m : ℝ) : UnforcedLeray.Short.IIIa.AdjE1.AdjChiUnique m :=
  adjChiUnique_of m kernelBSExists (weakFieldBandInt m) cellUnique weakDerivC1
    bandMulTest

end UnforcedLeray.Short.IIIa.AdjE1
