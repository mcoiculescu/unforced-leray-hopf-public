import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.GeoDDefs
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_7
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_10

/-!
# `PartIII-b:C/asrc/ra/9/1/2` : `DL2_proof`

Source of record: `the November 2 reference manuscript`,
lines 5034-5039, 4979-4980.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Cell `L²` bound for the `D_μ` geometric-error piece** (source lines 5034-5039, 4979-4980). -/
theorem DL2_proof (as : ℝ) (χf : ℝ → ℝ) : GeoDL2 as χf :=
  geoDL2_of as χf (geoDChartId as χf) (geoGCellL2 as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
