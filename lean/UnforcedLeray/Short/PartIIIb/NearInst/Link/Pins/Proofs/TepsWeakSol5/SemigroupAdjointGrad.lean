import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_4
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.SemigroupAdjointGrad.L0
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.SemigroupAdjointGrad.Smooth
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.SemigroupAdjointGrad.Grad
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.SemigroupAdjointGrad.Pair

/-!
# `SemigroupAdjointGrad` (task `PartIII-b:C/near/pins/3/5/4`)

Assembly of the four leaves `AdjL0` (`L0.lean`), `AdjSmooth` (`Smooth.lean`), `AdjGrad`
(`Grad.lean`) and `AdjPair` (`Pair.lean`) through `semigroupAdjointGrad_of`
(Sub `PartIII-b_C_near_pins_3_5_4`). Source `shorter-proof-2026-11-02.tex` 1675-1677, 1339-1362,
4139-4146.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem semigroupAdjointGrad : SemigroupAdjointGrad :=
  semigroupAdjointGrad_of adjL0 adjSmooth adjGrad adjPair

end UnforcedLeray.Short.PartIIIb.NearInst
