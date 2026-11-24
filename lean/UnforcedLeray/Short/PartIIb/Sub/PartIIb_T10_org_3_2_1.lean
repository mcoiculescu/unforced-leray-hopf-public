import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1_of
import UnforcedLeray.Short.PartIIa.Tasks.F05bSliceContOfDecay
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1.DecayOfFarBound
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1.NewtonJointFDeriv
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1.NewtonHessFar
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1.PhasePairLerayY

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem lerayTestSchwartz : UnforcedLeray.Short.IIb.LerayTestSchwartz :=
  lerayTestSchwartz_of PartIIa.sliceContOfDecay LTS.decayOfFarBound_proof
    LTS.newtonJointFDeriv_proof LTS.newtonHessFar_proof LTS.phasePairLerayY_proof

end UnforcedLeray.Short.IIb
