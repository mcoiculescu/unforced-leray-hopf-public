import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1.DerivY.Reduction
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1.DerivY.Bound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1.DerivY.IBP
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.SliceFieldElem

/-!
# `rawResidualDerivY_thm` (`PartIII-b:C/ward/12/3/1/2/4/1/2`)

Source of record: `the November 2 reference manuscript`,
lines 2542-2551 and 1206-1222 (and 1305-1322 for the ring residual).

Combines `derivY_of` (`DerivY/Reduction.lean`), `sliceFieldElem_proof` (`SliceFieldElem.lean`),
`ringResidualDerivBound_thm` (`DerivY/Bound.lean`), and `sliceIntegrationByParts_thm`
(`DerivY/IBP.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb

/-- Weak spatial derivative of the raw residual lies in `Y_{q₀}` (`RawResidualDerivY`). -/
theorem rawResidualDerivY_thm : UnforcedLeray.Short.PartIIIb.Concrete.RawResidualDerivY :=
  Concrete.derivY_of UnforcedLeray.Short.IIb.sliceFieldElem_proof
    Concrete.ringResidualDerivBound_thm Concrete.sliceIntegrationByParts_thm

namespace Concrete

export UnforcedLeray.Short.PartIIIb (rawResidualDerivY_thm)

end Concrete

end UnforcedLeray.Short.PartIIIb
