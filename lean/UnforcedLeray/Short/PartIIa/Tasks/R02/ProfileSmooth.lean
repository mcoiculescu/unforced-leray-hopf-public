import UnforcedLeray.Short.PartIIa.Sub.R02
import UnforcedLeray.Short.PartI.Sub.T01

/-!


Target: `lateProfileSmooth_of` proves `LateProfileSmooth` (`Short/PartII-a/Sub/R02.lean`, line 233)
from `PartI.TrainStreamSmooth` (`Short/PartI/Sub/T01.lean`, line 47).

Source of record: `the November 2 reference manuscript`, lines 261-288 (the train is
smooth for positive time).

Route. The profile point `(q, (η, s))` is sent to the train point `(s, (q, η))` by the linear
coordinate map `L`. The stream is `C^∞` on `Ioi 0 ×ˢ univ` in `(s, z)`, so its composition with `L`
is `C^∞` on `{x | 0 < x.2.2}`, which is the preimage of `Ioi 0 ×ˢ univ`. The pressure is `C^∞` on
`Ici 0 ×ˢ univ` (`IsTrain.smooth_p`), which contains `Ioi 0 ×ˢ univ`; restrict to that set first.

`trainProfile f x = f x.2.2 (x.1, x.2.1)` (`Units/B0190.lean`), so the composition is definitionally
`trainProfile`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0190

/-- The coordinate change `(q, (η, s)) ↦ (s, (q, η))` from profile variables to train variables. -/
theorem contDiff_profileToTrain :
    ContDiff ℝ ∞ (fun x : ProfilePoint => (x.2.2, (x.1, x.2.1))) := by
  fun_prop

/-- The coordinate change maps the profile half-space `{0 < s}` into `Ioi 0 ×ˢ univ`. -/
theorem mapsTo_profileToTrain :
    MapsTo (fun x : ProfilePoint => (x.2.2, (x.1, x.2.1)))
      {x : ProfilePoint | 0 < x.2.2} (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
  intro x hx
  exact Set.mk_mem_prod (show (0 : ℝ) < x.2.2 from hx) (Set.mem_univ _)

/-- **Target.** Profile form of stream smoothness: the stream and pressure profiles are `C^∞` on
`{0 < s}`. -/
theorem lateProfileSmooth_of (h : UnforcedLeray.Short.PartI.TrainStreamSmooth) :
    LateProfileSmooth := by
  unfold LateProfileSmooth
  intro ν c hν hc tr hb
  have hψ := h ν c hν hc tr hb
  have hp := tr.isTrain.smooth_p
  have hp' : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.p x.1 x.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hp.mono (Set.prod_mono Set.Ioi_subset_Ici_self Set.Subset.rfl)
  constructor
  · exact ContDiffOn.comp hψ contDiff_profileToTrain.contDiffOn mapsTo_profileToTrain
  · exact ContDiffOn.comp hp' contDiff_profileToTrain.contDiffOn mapsTo_profileToTrain

end UnforcedLeray.Short.PartIIa
