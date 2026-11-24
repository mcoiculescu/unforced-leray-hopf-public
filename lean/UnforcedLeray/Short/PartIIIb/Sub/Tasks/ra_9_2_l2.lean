import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvGeoSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4.L2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.Eq
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.Envelope

/-!
# `ConvL2_proof` (`PartIII-b:C/asrc/ra/9/2/2`)

Source of record: `the November 2 reference manuscript`, lines 5034-5044.
Composes `geoConvL2_of`, `convChartEq`, `convGL2_of`, `convGEnvelope`, and `gradLatticeL2`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ConvL2_proof (as : ℝ) (χf : ℝ → ℝ) : GeoConvL2 as χf :=
  geoConvL2_of as χf (convChartEq as χf) (convGL2_of as χf (convGEnvelope as χf) gradLatticeL2)

end UnforcedLeray.Short.PartIIIb.Concrete

end
