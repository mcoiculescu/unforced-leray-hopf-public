import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.HpAC2

/-!
# `PartIII-b:C/asrc/ra/9/1/1` : `GeoDMeas` (task `DMeas_proof`)

Source of record: `the November 2 reference manuscript` lines 5034-5039, 4979-4980.
Closes `GeoDMeas` by applying `DMeas_of` to `affineLiftReg` (task `PartIII-b:C/asrc/ra/5`)
and `hpAC2` (task `PartIII-b:C/asrc/ra/5/5`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Lemma 1** (measurability and support of the `D_μ` piece), unconditional form. -/
theorem DMeas_proof (as : ℝ) (χf : ℝ → ℝ) : GeoDMeas as χf :=
  DMeas_of as χf (affineLiftReg as χf) (hpAC2 as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
