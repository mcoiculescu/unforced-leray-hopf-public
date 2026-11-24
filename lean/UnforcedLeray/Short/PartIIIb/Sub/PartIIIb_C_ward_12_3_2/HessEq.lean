import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.HessEqSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.RawDeriv2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.InletIBP2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Lin2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Quad2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.RawSmoothBdd3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8.G2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1.WeakId
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5.IBP.MemLp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5.IBP.Identity
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawPeriodicAll
import UnforcedLeray.Short.PartIIa.Tasks.R07BoundedDerivs

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Assembly of `BgCorrHessEq` (source 2525-2562, design ORG:ward/bg-bootstrap). -/
theorem bgCorrHessEq : BgCorrHessEq :=
  bgCorrHessEq_of gEBodyUniqueSol_proof (gERaw2_of rawResidualWeakIdentity_thm rawResidualDeriv2Y)
    (gEInlet2_of (gEInletIBP2_of inletFnMemLp inletIBPIdentity))
    (gELin2_of (rawSmoothBdd3_of rawJointSmooth rawPeriodicAll
      (rawDerivBdd3_of (ringLiftBdd3_of_ringBoundedDerivs UnforcedLeray.Short.PartIIa.ringBoundedDerivs))))
    gEQuad2

end UnforcedLeray.Short.PartIIIb.Concrete
