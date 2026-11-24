import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_3.VsumC1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.HpAC2

/-!
# `PartIII-b:C/asrc/ra/8/3/3` : `RTrainMeas` from `HpAC2` and `C¹` of `Σ_jV_j`

Source: `the November 2 reference manuscript`
5023-5028, 4978.  Leaves: `hpAC2` (ra/5/5) and `vsumC1` (ra/8/3/3/1).
-/

set_option autoImplicit false

/-- Top-level name of `RTrainMeas` (source 5023-5028, 4978). -/
theorem rTrainMeas (as : ℝ) (χf : ℝ → ℝ) : UnforcedLeray.Short.PartIIIb.Concrete.RTrainMeas as χf :=
  UnforcedLeray.Short.PartIIIb.Concrete.rTrainMeas_of as χf
    (UnforcedLeray.Short.PartIIIb.Concrete.hpAC2 as χf) vsumC1
