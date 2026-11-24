import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.DictVel
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.PairXCont
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.XSolExtend
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.SemigroupAdjointGrad
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.XSolDil

/-!
# `RepsVecSolenoidal` (task `PartIII-b:C/near/pins/3/5`)

Assembles the five leaves `dictVel`, `pairXCont`, `xSolExtend`, `semigroupAdjointGrad`,
`xSolDil` through `repsVecSolenoidal_of`, `physResSol_of` and `xSolSemigroup_of`
(Sub file `PartIII-b_C_near_pins_3_5`). Source `shorter-proof-2026-11-02.tex` 1675-1677,
2666-2668, 2683, 1339-1362, 4139-4146.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem repsVecSolenoidal : RepsVecSolenoidal :=
  repsVecSolenoidal_of dictVel
    (physResSol_of pairXCont (xSolSemigroup_of xSolExtend semigroupAdjointGrad)) xSolDil

end UnforcedLeray.Short.PartIIIb.NearInst
