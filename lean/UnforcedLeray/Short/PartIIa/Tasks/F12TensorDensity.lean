import UnforcedLeray.Short.PartIIa.Sub.F12
import UnforcedLeray.Short.PartIIa.Tasks.F12aSmoothSymSubmodule
import UnforcedLeray.Short.PartIIa.Tasks.F12cSmoothSymSeparation

/-!
# Part II-a, task `PartII-a:F12`: unconditional density of smooth symmetric tensors

Final assembly of the completion from smooth tensors (source of record:
`the November 2 reference manuscript`, lines 1546-1586).

`smoothTensorsDense_of` (`Sub/F12.lean`) reduces `SmoothTensorsDense` to two leaves:

* `smoothSymSubmodule : SmoothSymSubmodule` (`Tasks/F12aSmoothSymSubmodule.lean`, task `F12/1`);
* `smoothSymSeparation : SmoothSymSeparation` (`Tasks/F12cSmoothSymSeparation.lean`, task `F12/3`,
  from `phaseInnerEqPairing`, task `F12/2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- Smooth symmetric phase tensors are dense in `Y_2(Sym_3)` (`StatementsFree.lean`). -/
theorem smoothTensorsDense : SmoothTensorsDense :=
  smoothTensorsDense_of smoothSymSubmodule smoothSymSeparation

end UnforcedLeray.Short.PartIIa
