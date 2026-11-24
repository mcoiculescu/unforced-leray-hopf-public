import UnforcedLeray.Short.PartI.Sub.T02_1_2
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.Datum
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.SeedDerivative
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.BaseDerivative
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.StepDerivative
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.SmoothPathsPersistent

/-!
# Part I, task `PartI:T02/1/2`: unconditional `H^k` persistence (`HkPersistence`)

Source of record: `the November 2 reference manuscript`, lines 261-288.
Assembly of the six accepted leaves through `hkPersistence_of` (`Short/PartI/Sub/T02_1_2.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem hkPersistence : HkPersistence :=
  hkPersistence_of projectedDatumPersistent seedDerivative bilDuhamelDerivative baseDerivative
    stepDerivative smoothPathsPersistent

end UnforcedLeray.Short.PartI
