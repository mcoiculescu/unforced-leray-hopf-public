import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_4
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.FlatStressFree.BodyColumnTransport
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.FlatStressFree.TensorDivIBP
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.FlatStressFree.FreeEnergyFlatSq
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.FlatStressFree.RealTensorTestApprox
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.FlatStressFree.BlkNormLe
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.FlatStressFree.VelNormLe
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.BodyColumnFlat
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy

/-!
# `flatStressFree` (item `PartIII-b:C/near/delta/8/2/3/4`)

Source `the November 2 reference manuscript`
lines 1655-1656, 1686-1689, 3427-3440.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem flatStressFree : FlatStressFree :=
  flatStressFree_of
    (bodyColumnTransport_of UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.bodyColumnFlat)
    tensorDivIBP
    (freeEnergyFlatSq_of UnforcedLeray.Short.IIIa.weightedEnergyIdentity)
    realTensorTestApprox
    blkNormLe
    velNormLe

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
