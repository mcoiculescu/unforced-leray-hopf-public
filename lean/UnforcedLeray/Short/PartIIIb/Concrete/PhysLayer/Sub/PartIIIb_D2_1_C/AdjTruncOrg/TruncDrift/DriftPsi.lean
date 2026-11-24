import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncDrift.DriftPsiCorr

/-!
# `driftPsi`: the corrected weak drift of the stream potential (source 1351-1362, 1470-1480)

`DriftPsi` (in `Sub/PartIII-b_IIIb-D2_1_3_1_2_1_12.lean`) now carries the corrected constant
`μ + ½`; `DriftPsiCorr` is an abbreviation for it and `driftPsiCorr` proves it. This file states the
target `driftPsi : DriftPsi` by that proof.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem driftPsi : DriftPsi := driftPsiCorr

end UnforcedLeray.Short.PartIIIb.Concrete
