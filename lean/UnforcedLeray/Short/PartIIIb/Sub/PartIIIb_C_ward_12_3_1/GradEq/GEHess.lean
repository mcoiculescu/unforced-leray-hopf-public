import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.FreeGraphHessian
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.Compose
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.WindowBackHess
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.WindowHessAEMeas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.WindowHessUnique
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.WindowHessPoU
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.WindowHessPeriodic
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.WindowTestIdentityHess

/-!
# `GEHess` (source 2531, `D²w ∈ Y_p`)

Task `PartIII-b:C/ward/12/3/1/2/2`.  Source of record
`the November 2 reference manuscript`,
lines 1377-1442 (free heat estimate and window reduction) and 2531 (`D²w ∈ Y_p`).

The proof composes the proved leaves: `FreeGraphHessian` (`Hess/FreeGraphHessian.lean`) gives
`GEHess` through `gEHess_of_freeGraphHessian`; the body Hessian bound is obtained from the
window leaves via `bodyHessianBound_of`, `localWindowHess_of`, `globalHessFieldWindowBound_of`
and `hessFieldToYRep_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`GEHess`** (source 2531): the Cartesian Hessian `D²w` of a body solution lies in `Y_p`. -/
theorem gEHess : GEHess :=
  gEHess_of_freeGraphHessian (freeGraphHessian_of (bodyHessianBound_of
    (localWindowHess_of windowBackHess)
    (globalHessFieldWindowBound_of windowHessAEMeas windowHessUnique windowHessPoU
      (windowHessPeriodic_of windowHessUnique))
    (hessFieldToYRep_of windowTestIdentityHess)))

end UnforcedLeray.Short.PartIIIb.Concrete
