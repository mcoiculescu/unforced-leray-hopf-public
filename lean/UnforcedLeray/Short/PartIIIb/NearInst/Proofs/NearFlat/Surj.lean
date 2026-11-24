import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearFlat.BridgeAssembly

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem nearD0Surj_of (hPS : UnforcedLeray.Short.IIIa.PolyStressCorollary)
    (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique) (hA : FlatMultFunBound) :
    NearD0Surj :=
  nearD0Surj_of_bridge hPS hU hA

#print axioms nearD0Surj_of

end UnforcedLeray.Short.PartIIIb.NearInst
