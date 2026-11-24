import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K2a
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K2b
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K2c

/-!
# `PartIII-a:T21/2/2/3/6/1/2`: `WeakFieldBandInt` from three leaves

Assembles `weakFieldBandInt_of` with the three proved leaves `testMeasF` (K2a),
`testMeasDeriv` (K2b) and `bandIntOfL2` (K2c).
Source: `the November 2 reference manuscript` lines 3052-3058, 3044-3047.
-/

set_option autoImplicit false

theorem weakFieldBandInt (m : ℝ) : UnforcedLeray.Short.IIIa.AdjE1.WeakFieldBandInt m :=
  UnforcedLeray.Short.IIIa.AdjE1.weakFieldBandInt_of m testMeasF testMeasDeriv bandIntOfL2
