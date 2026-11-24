import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_2
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_2_meas
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_2_l2

/-!
# `PartIII-b:C/asrc/ra/9/2` : `rAGeoConv`

Source of record: `the November 2 reference manuscript`, lines 5040-5044, 2076-2077.
Combines `ConvMeas_proof` (`PartIII-b:C/asrc/ra/9/2/1`) and `ConvL2_proof` (`PartIII-b:C/asrc/ra/9/2/2`)
via `rAGeoConv_of` to establish `RAGeoConvLeaf`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Support/measurability and cell `L²` bound for the convection geometric-error piece**
(source lines 5040-5044, 2076-2077). -/
theorem rAGeoConv (as : ℝ) (χf : ℝ → ℝ) : RAGeoConvLeaf as χf :=
  rAGeoConv_of as χf (ConvMeas_proof as χf) (ConvL2_proof as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
