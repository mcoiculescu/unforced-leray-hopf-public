import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4.ChartEq
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4.Bound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.PsiC1

/-!
# `PartIII-b:C/asrc/ra/9/4` : the pressure leaf `RAGeoGradLeaf` (source 5039-5043)

Closes the target `rAGeoGrad` by applying `rAGeoGrad_of` (in `PartIII-b_C_asrc_ra_9_4`) to the
pointwise chart identity `geoGradChartEq`, the `C¹` regularity `affPsiC1` of `sΨ_A`, and the
remainder bound `gradRemBound`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Leaf Grad** (source 5039-5043): the pressure leaf `RAGeoGradLeaf` holds for all `as`, `χf`. -/
theorem rAGeoGrad (as : ℝ) (χf : ℝ → ℝ) : RAGeoGradLeaf as χf :=
  rAGeoGrad_of as χf geoGradChartEq (affPsiC1 as χf) (gradRemBound as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
