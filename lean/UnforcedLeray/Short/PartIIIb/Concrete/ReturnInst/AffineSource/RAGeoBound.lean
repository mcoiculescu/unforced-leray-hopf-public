import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAGeoD
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAGeoConv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAGeoFE
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAGeoGrad

/-!
# `PartIII-b:C/asrc/ra/9` : `RAGeoBound` (source 5034-5044)

Source of record: `the November 2 reference manuscript` (73 pages).
Assembles `RAGeoBound` from the four ring-chart piece bounds `rAGeoD`, `rAGeoConv`, `rAGeoFE`,
and `rAGeoGrad` via `raGeoBound_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem raGeoBound (as : ℝ) (χf : ℝ → ℝ) : RAGeoBound as χf :=
  raGeoBound_of as χf (rAGeoD as χf) (rAGeoConv as χf) (rAGeoFE as χf) (rAGeoGrad as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
