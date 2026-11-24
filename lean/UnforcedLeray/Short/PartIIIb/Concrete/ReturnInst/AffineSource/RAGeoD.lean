import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_meas
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_l2

/-!
# `PartIII-b:C/asrc/ra/9/1` : `rAGeoD`

Source of record: `the November 2 reference manuscript`, lines 5034-5039, 4979-4980.
Combines `DMeas_proof` (`PartIII-b:C/asrc/ra/9/1/1`) and `DL2_proof` (`PartIII-b:C/asrc/ra/9/1/2`)
via `rAGeoD_of` to establish `RAGeoDLeaf`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Support/measurability and cell `L²` bound for the `D_μ` geometric-error piece**
(source lines 5034-5039, 4979-4980). -/
theorem rAGeoD (as : ℝ) (χf : ℝ → ℝ) : RAGeoDLeaf as χf :=
  rAGeoD_of as χf (DMeas_proof as χf) (DL2_proof as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
