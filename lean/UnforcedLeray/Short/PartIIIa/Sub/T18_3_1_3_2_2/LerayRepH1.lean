import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.Assembly
import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.SliceTested
import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.P0Rep

/-!
# Part III-a, `PartIII-a:T18/3/1/3/2/2/org`: `LMDerivRepAEH1`, unconditional

Source of record: `the November 2 reference manuscript` lines 3427-3440, 3541-3552.
The weak derivative `u'(s) = -(μ/s) u_k(s) + 𝒫₀ Z(s)` of `u_k = J_k b`, for a mollifier with the
properties `LMMollH1`, and the pairing identity for a.e. `s > 0`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

/-- **`LMDerivRepAE` for mollifiers with the properties `LMMollH1`** (SP 3427-3440, 3541-3552). -/
theorem lmDerivRepAEH1 : LMDerivRepAEH1 :=
  lmDerivRepAEH1_of lmP0CAdj lmP0CFix lmJWeakDiv lmH1Test lmSliceTested lmDivJMeasRep lmP0Rep
    lmUkL2Loc lmYtL2Loc lmUDerL2Loc lmIpWeightedInt lmPairingSlice lmSliceTensor

#print axioms lmDerivRepAEH1

end UnforcedLeray.Short.IIIa
