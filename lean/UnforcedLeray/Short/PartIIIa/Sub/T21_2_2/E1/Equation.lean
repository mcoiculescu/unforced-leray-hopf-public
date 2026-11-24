import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation.A_Diff
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation.B_ChiC1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation.C_ChiPer
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation.D_ChiInter
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakPointwise

/-!
# `PartIII-a:T21/2/2/3/2`: the classical moving adjoint equation (assembly)

Source of record: `the November 2 reference manuscript` (SP) lines 2854-2865,
3052-3060. `movAdjEquation_of` (in `PartIIIa_T21_2_2_3_2`) reduces `MovAdjEquation m` to the
four leaves `MvPhiDiff`, `MvChiC1`, `MvChiPer`, `MvChiInter` and the classical weak identity
`AdjWeakPointwise m`; each leaf and `adjWeakPointwise` is already proved.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- **Leaf `.../3/2` assembly**: the classical moving adjoint equation for `8 < m`, from the four
leaves and `adjWeakPointwise`. -/
theorem movAdjEquation (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.AdjE1.MovAdjEquation m :=
  movAdjEquation_of m (UnforcedLeray.Short.IIIa.adjWeakPointwise m) (mvPhiDiff m) (mvChiC1 m)
    (mvChiPer m) (mvChiInter m)

end UnforcedLeray.Short.IIIa.AdjE1
