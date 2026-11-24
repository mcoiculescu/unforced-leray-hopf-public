import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7_5
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.PairInt
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.BSExists
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.WeakMeas
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.KerAdjElt
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.PdEcCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.FieldDiffSmall

/-!
# `PartIII-a:T21/2/7/1/7/5`: `LocAdjStrongCont` from its components

Source: `the November 2 reference manuscript` lines 3052-3058, 2875-2896.

The proof is the assembly `locAdjStrongCont_of` (`Sub/PartIII-a_T21_2_7_1_7_5.lean`) applied to
the compiled component theorems `locPairInt`, `locBSExists`, `locKerAdjElt`, `locWeakMeas`,
`locFieldDiffSmall` and `locPdEcCont`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem locAdjStrongCont (m : ℝ) (hm : 8 < m) (hK : KernelAdjointBound m) (hU : LocCylUniq) (hF : LocFieldBound m) : LocAdjStrongCont m :=
  locAdjStrongCont_of m (locPairInt m hm) hF hU locBSExists (locKerAdjElt m hm hK locWeakMeas)
    (locFieldDiffSmall m hm locPdEcCont)

end UnforcedLeray.Short.IIIa
