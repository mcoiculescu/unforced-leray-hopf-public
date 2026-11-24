import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RADefs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_6.LiftsEquiv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_6.DmuEquiv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_6.DivSymEquiv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_6.GradEquiv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_6.AxiNoSwirlOfEquiv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_6.LiftsPer

/-!
# `PartIII-b:C/asrc/ra/6` : `RAPhysAxi` (target `raPhysAxi`)

Source of record: `the November 2 reference manuscript` lines 121-124,
2666-2668, 4995-4997.  Closes `RAPhysAxi` by applying the reduction `raPhysAxi_of` (in the Sub file
`PartIII-b_C_asrc_ra_6`) to the accepted leaves: `affineLiftReg` (ra/5), `raLiftsEquiv`,
`physDmuEquiv`, `physDivSymEquiv`, `physGradEquiv`, `axiNoSwirlOfEquiv`, `raLiftsPer`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`𝔯_A` is axisymmetric without swirl and periodic** (source 2666-2668, 4995-4997), closed by
the reduction `raPhysAxi_of` applied to the accepted leaves. -/
theorem raPhysAxi (as : ℝ) (χf : ℝ → ℝ) : RAPhysAxi as χf :=
  raPhysAxi_of as χf (affineLiftReg as χf) (raLiftsEquiv as χf) physDmuEquiv physDivSymEquiv
    physGradEquiv axiNoSwirlOfEquiv (raLiftsPer as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
