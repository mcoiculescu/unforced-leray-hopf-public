import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2.WDeriv
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2.ScaleW
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2.ScaleR
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2.MvPhiDt
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2.PsiDiff
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2.RateAlg
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2.PsiInt
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.BasicReg
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.TrainV

/-!
# `PartIII-a:T21/2/2/3/5/3/2` (`E1PhysRate`): assembly

Source of record: `the November 2 reference manuscript` (SP) lines 2945-2957,
3060-3062, 3137-3139. The statement `E1PhysRate m` is the Prop `E1PhysRate` of
`Sub/PartIIIa_T21_2_2_3_5_3.lean`. The proof is the assembly `e1PhysRate_of` of
`Sub/PartIII-a_T21_2_2_3_5_3_2.lean` applied to the seven leaves and the compiled
regularity inputs `movAdjBasicReg` (`E1/BasicReg.lean`) and `movingTrainVReg` (`E1/TrainV.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem e1PhysRate (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.AdjE1.E1PhysRate m :=
  e1PhysRate_of m (physWDeriv m) (e1ScaleW m) (e1ScaleR m) (mvPhiDt m) psiDiff
    (e1RateAlg m) (e1PsiInt m hm) (movAdjBasicReg m hm) movingTrainVReg

end UnforcedLeray.Short.IIIa.AdjE1
