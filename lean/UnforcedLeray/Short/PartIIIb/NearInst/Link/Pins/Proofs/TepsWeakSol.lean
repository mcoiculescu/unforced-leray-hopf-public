import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_3
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol3
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol4
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5

/-!
# `tepsWeakSol` (task `PartIII-b:C/near/pins/3`)

Source `the November 2 reference manuscript` 1675-1677, 1339-1362, 4139-4146.

Applies `tepsWeakSol_of` to the five proved leaves (`pepsRealForm`, `pepsSolenoidal`,
`pepsLerayInvisible`, `repsVecEquation`, `repsVecSolenoidal`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem tepsWeakSol : TepsWeakSol :=
  tepsWeakSol_of pepsRealForm pepsSolenoidal pepsLerayInvisible repsVecEquation repsVecSolenoidal

end UnforcedLeray.Short.PartIIIb.NearInst
