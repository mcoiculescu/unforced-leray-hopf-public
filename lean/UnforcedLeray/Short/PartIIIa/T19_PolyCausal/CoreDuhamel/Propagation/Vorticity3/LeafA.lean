import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2_3_2_3_1
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity3.LeafA.Nice
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity3.LeafA.Density

/-!
# Part III-a, task `PartIII-a:T19/2/3/2/3/1`: `CoreDuhamelRep` (conditional assembly)

Source of record: `the November 2 reference manuscript` (SP), lines 3481-3491.

The submodule `UnforcedLeray.Short.«PartIII-a».Sub.«PartIII-a_T19_2_3_2_3_1»` proves
`coreDuhamelRep_of`, assembling `CoreDuhamelRep` from the two leaf propositions:

* `CoreDuhamelNice` (`PartIII-a:T19/2/3/2/3/1/1`, SP 3427-3440, 3481-3491, 3541-3545): Duhamel
  representation of `corePerturbVort` for nice forces `NiceForce (ν ^ (-2 : ℝ)) F`.
* `CoreDuhamelDensity` (`PartIII-a:T19/2/3/2/3/1/2`, SP 3427-3440, 3481-3496, 3518-3527):
  passage to the `Z^{-1}_{9,c}` density limit along `CoreDuhamelRepSub.NiceDuhamelApprox`.

Given `coreDuhamelNice_proof : CoreDuhamelNice` and `coreDuhamelDensity_proof : CoreDuhamelDensity`,
`coreDuhamelRep_proof_of coreDuhamelNice_proof coreDuhamelDensity_proof` gives the target
`coreDuhamelRep_proof : UnforcedLeray.Short.IIIa.CoreDuhamelRep`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem coreDuhamelRep_proof_of (hNice : CoreDuhamelNice) (hLim : CoreDuhamelDensity) :
    UnforcedLeray.Short.IIIa.CoreDuhamelRep :=
  coreDuhamelRep_of hNice hLim

theorem coreDuhamelRep_proof : UnforcedLeray.Short.IIIa.CoreDuhamelRep :=
  coreDuhamelRep_of coreDuhamelNice_proof coreDuhamelDensity_proof

end UnforcedLeray.Short.IIIa
