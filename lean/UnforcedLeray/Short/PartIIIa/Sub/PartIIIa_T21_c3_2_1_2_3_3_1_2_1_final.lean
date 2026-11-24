import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L2_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_2_1_leaf1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_2_1_leaf2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_2_1_leaf3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_2_1_leaf4

theorem frameTestedDuhamel (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.ComplMildTestedSplit.FrameTestedDuhamel κ :=
  UnforcedLeray.Short.IIIa.ComplMildTestedSplit.frameTestedDuhamel_of' κ
    (UnforcedLeray.Short.IIIa.ComplMildTestedSplit.FrameDuhamelSub.frameVecReg κ)
    (UnforcedLeray.Short.IIIa.ComplMildTestedSplit.FrameDuhamelSub.frelDualRep κ)
    (UnforcedLeray.Short.IIIa.ComplMildTestedSplit.FrameDuhamelSub.frameDualCore κ)
    UnforcedLeray.Short.IIIa.ComplMildTestedSplit.FrameDuhamelSub.dualTestSep
