import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_8
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_8_1
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_8_2

/-!
# `PartIII-b:C/asrc/ra/9/1/2/8` : `geoGPointwise`

Source of record: `the November 2 reference manuscript`,
lines 5034-5039, 4979-4980.  `G = Dc ν μ Θ + ringRem ν ε b`.  The assembly `geoGPointwise_of` is applied
to `geoDcThetaBound` (task `ra_9_1_2_8_1`) and `geoRingRemBound` (task `ra_9_1_2_8_2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`geoGPointwise`** (source 5034-5039, 4979-4980): the assembly `geoGPointwise_of` applied to the
two bounds `geoDcThetaBound` and `geoRingRemBound`. -/
theorem geoGPointwise (as : ℝ) (χf : ℝ → ℝ) : GeoGPointwise as χf :=
  geoGPointwise_of as χf (geoDcThetaBound as χf) (geoRingRemBound as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
