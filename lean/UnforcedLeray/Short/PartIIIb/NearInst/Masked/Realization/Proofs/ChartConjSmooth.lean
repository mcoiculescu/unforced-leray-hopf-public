import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.ChartConj
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.CartLiftIsTest
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.CartTestDivMemLp
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.PepsCCplx
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.LiftVecCplx
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DivLiftPoint

/-!
# `ChartConjSmooth` (source 1639-1675, 2681-2691, 3893-3906)

The conjugated chart-Cartesian comparison `ChartConjSmooth` follows from the five leaf
propositions `CartLiftIsTest`, `CartTestDivMemLp`, `PepsCCplx`, `LiftVecCplx`, `DivLiftPoint`
through `chartConjSmooth_of` (ChartConj.lean).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- **`ChartConjSmooth`** (assembled from the five leaves). -/
theorem chartConjSmooth : ChartConjSmooth :=
  chartConjSmooth_of cartLiftIsTest cartTestDivMemLp pepsCCplx liftVecCplx divLiftPoint

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
