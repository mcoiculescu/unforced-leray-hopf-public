import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1_4.Assembly
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1_4.PeriodAvg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1_4.HalfPlane
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1_4.SpacePolar
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1_4.SlicesChange

/-!
# Exact `-5/2` change of variables (`PartIII-b:C/near/masked/14/2/3/1/4`; source 2683, 3604-3610,
3996-4011)

Composition of the periodic average in `q` (`periodAvg`) with the half-plane-to-`ℝ³` change of
variables (`halfPlaneToSpace_of`, built from `spacePolar` and `slicesChange`).
-/

theorem outChangeVarExp : UnforcedLeray.Short.PartIIIb.NearInst.Masked.OutChangeVarExp :=
  UnforcedLeray.Short.PartIIIb.NearInst.Masked.outChangeVarExp_of
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.periodAvg
    (UnforcedLeray.Short.PartIIIb.NearInst.Masked.halfPlaneToSpace_of
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.spacePolar
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.slicesChange)
