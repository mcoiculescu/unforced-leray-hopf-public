import UnforcedLeray.Short.PartI.Sub.PartI_T01_8
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanStreamDeriv

/-!
# Part I, task `PartI:T01/8`: the averaged momentum equation for the mean stream

Source of record: `the November 2 reference manuscript`, lines 397-404 (`sct:mean`).
The statement `TrainMeanMomentumEta` is defined in `Short/PartI/Sub/T01.lean`.

Route. `trainMeanStreamDeriv` (`PartI:T01/2`) gives `S_s = g - ν ∂_η \bar v₁` for BUC trains,
and `trainMeanMomentumEta_of` (`Sub/PartI_T01_8.lean`) turns this into the `η`-derivative
identity `S_s - ν S_ηη - g ≡ 0`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **`PartI:T01/8`, `TrainMeanMomentumEta`** (source lines 397-404). -/
theorem trainMeanMomentumEta : TrainMeanMomentumEta :=
  trainMeanMomentumEta_of trainMeanStreamDeriv

end UnforcedLeray.Short.PartI
