import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_2.Pointwise
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_2.EnvL2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_2.AffMBdd
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.HpAC2

/-!
# `PartIII-b:C/asrc/ra/8/3/2` : `HpAL2` from three leaves and `HpAC2`

Source: `the November 2 reference manuscript`
4963-4977, 5029-5032.  The leaves are `hpAPointwise` (ra/8/3/2/1), `gEnvL2` (ra/8/3/2/3),
`affMBdd` (ra/8/3/2/2) and `hpAC2` (ra/5/5).
-/

set_option autoImplicit false

/-- Top-level name of `HpAL2` (source 4963-4977, 5029-5032). -/
theorem hpAL2 (as : ℝ) (χf : ℝ → ℝ) : UnforcedLeray.Short.PartIIIb.Concrete.HpAL2 as χf :=
  UnforcedLeray.Short.PartIIIb.Concrete.hpAL2_of as χf
    (UnforcedLeray.Short.PartIIIb.Concrete.hpAC2 as χf) hpAPointwise
    UnforcedLeray.Short.PartIIIb.Concrete.gEnvL2
    (UnforcedLeray.Short.PartIIIb.Concrete.affMBdd as χf)
