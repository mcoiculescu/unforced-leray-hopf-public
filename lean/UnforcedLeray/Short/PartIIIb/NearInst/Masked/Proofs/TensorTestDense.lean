import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_6
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.SmoothCellDenseProof
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.PeriodizeTensorTest

/-!
# `PartIII-b:C/near/masked/6`: `TensorTestDense` (source 1678)

Composition of the two leaves: `SmoothCellDense` (`SmoothCellDenseProof.lean`) and
`PeriodizeIsTensorTest` (`PeriodizeTensorTest.lean`), through `tensorTestDense_of`
(`Sub/PartIII-b_C_near_masked_6.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem tensorTestDense : TensorTestDense :=
  tensorTestDense_of smoothCellDense periodizeIsTensorTest

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
