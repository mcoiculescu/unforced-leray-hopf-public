import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Minkowski
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Rep

/-!
# `PartIII-a:T21/c3/3/1/1/2`: `ComplMildFreeBound`

Source of record: `the November 2 reference manuscript` (SP), lines 2919-2925,
2937-2958.

Assembles `complMildFreeBound` from `complMildFreeBound_of`, `xNormIntegralLe`, and
`complDuhamelRep`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem complMildFreeBound (κ : PlanarFrameKernels) (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    (ν m b K : ℝ) (hν : 0 < ν) (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ C_loc C_H0 : ℝ) :
    UnforcedLeray.Short.IIIa.ComplFreeRateSub.ComplMildFreeBound κ P ν m b K hν hF tr t₁ t₂
      C_loc C_H0 :=
  ComplFreeRateSub.complMildFreeBound_of κ P ν m b K hν hF tr t₁ t₂ C_loc C_H0
    _root_.xNormIntegralLe (ComplFreeRateSub.complDuhamelRep κ P ν m b K hν hF tr t₁ t₂ C_loc C_H0)

end UnforcedLeray.Short.IIIa
