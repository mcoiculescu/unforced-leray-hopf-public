import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_4
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointSmoothing.HigherCont.Defs
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointSmoothing.HigherCont.ChiBound
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointSmoothing.HigherCont.SourceBound
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointSmoothing.HigherCont.IntegratedH1
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointSmoothing.HigherCont.TimeCont

/-!
# `AdjointWeakHigherCont` (`PartIII-a:T21/2/7/2/4`)

Reduces `AdjointWeakHigherCont` (SP lines 3060-3073) to the four decomposed leaf propositions in
`Sub/PartIII-a_T21_2_7_2_4.lean` via `adjointWeakHigherCont_of_parts`:
- `AdjHigherChiBound m` (`PartIII-a:T21/2/7/2/4/1`, `HigherCont/ChiBound.lean`),
- `AdjHigherSourceBound m` (`PartIII-a:T21/2/7/2/4/2`, `HigherCont/SourceBound.lean`),
- `AdjFieldIntegratedH1 m` (`PartIII-a:T21/2/7/2/4/3`, `HigherCont/IntegratedH1.lean`),
- `AdjHigherTimeCont m` (`PartIII-a:T21/2/7/2/4/4`, `HigherCont/TimeCont.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem adjointWeakHigherCont (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.AdjointWeakHigherCont m :=
  adjointWeakHigherCont_of_parts m hm (adjHigherChiBound m hm) (adjHigherSourceBound m hm)
    (adjFieldIntegratedH1 m hm) (adjHigherTimeCont m hm)

end UnforcedLeray.Short.IIIa

