import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2.ENear4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2.Deriv2Bound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2.EFar4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2.ProdHom2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R07BoundedDerivs

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Source: shorter-proof-2026-11-02.tex lines 2542-2551. -/
theorem gEInletIBP2_of (h1 : InletFnMemLp) (h2 : InletIBPIdentity) : GEInletIBP2 :=
  gEInletIBP2_of_sub rawJointSmooth
    (rawDerivBdd3_of (ringLiftBdd3_of_ringBoundedDerivs UnforcedLeray.Short.PartIIa.ringBoundedDerivs))
    inletENearJets4 inletSrcDeriv2Bound inletEFarHom4 inletFn2FarOfHom h1 h2

end UnforcedLeray.Short.PartIIIb.Concrete
