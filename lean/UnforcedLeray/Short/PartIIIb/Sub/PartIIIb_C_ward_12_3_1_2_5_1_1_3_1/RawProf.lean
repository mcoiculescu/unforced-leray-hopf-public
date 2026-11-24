import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1.VelJoint
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1.MeanStream
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1.StreamJoint
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1.RawSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1.RawJet

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/4/1`: `rawProfFarJet`

Source `the November 2 reference manuscript`
1206-1222. Assembles `rawProfFarJet` from `rawProfFarJet_of`, `velJointJetsFixed`,
`streamJointJetsPoly`, `rawProfSmoothGen`, and `rawProfJetGen`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rawProfFarJet : RawProfFarJet :=
  rawProfFarJet_of velJointJetsFixed streamJointJetsPoly rawProfSmoothGen rawProfJetGen

end UnforcedLeray.Short.PartIIIb.Concrete
