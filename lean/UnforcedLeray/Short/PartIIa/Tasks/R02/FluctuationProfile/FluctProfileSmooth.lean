import UnforcedLeray.Short.PartIIa.Sub.R02_2
import UnforcedLeray.Short.PartI.Sub.T01

/-!
# Part II-a, task `PartII-a:R02/2/5` (`FluctProfileSmooth`): smoothness of the stream fluctuation

Target: `fluctProfileSmooth_of` proves `FluctProfileSmooth` (`Short/PartII-a/Sub/R02_2.lean`,
line 133) from `LateProfileSmooth` (`Short/PartII-a/Sub/R02.lean`, line 233) and `HmeanContDiff`
(`Short/PartI/Sub/T01.lean`, line 62).

Source of record: `the November 2 reference manuscript`, lines 397-404 (the mean
stream `S = \bar ψ`) and 439-446 (the profile form of the fluctuation).

Route.

1. The profile form `trainProfile tr.ψ` is `C^∞` on `{0 < s}` (hypothesis `hS`). Composing with the
   linear map `x ↦ (x.2.1, (x.2.2, x.1))` from `Ioi 0 ×ˢ univ` into `{0 < s}` gives the train form
   `(s, z) ↦ tr.ψ s z` on `Ioi 0 ×ˢ univ`.
2. `HmeanContDiff` (hypothesis `hH`) applied to `tr.ψ` gives smoothness of
   `(s, η) ↦ hmean c (tr.ψ s) η`, which is `meanStream tr s η` by definition.
3. `contDiffOn_trainProfile_of_eta` gives the profile form of `meanStream tr`.
4. `trainProfile` of the pointwise difference is the difference of the two profile forms, so
   `ContDiffOn.sub` concludes.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0190

/-- **Target.** The stream fluctuation `ψ̃ = ψ - \bar ψ` is `C^∞` in profile form on `{0 < s}`,
from profile smoothness of the stream and smoothness of the horizontal average. -/
theorem fluctProfileSmooth_of (hS : UnforcedLeray.Short.PartIIa.LateProfileSmooth)
    (hH : UnforcedLeray.Short.PartI.HmeanContDiff) :
    UnforcedLeray.Short.PartIIa.FluctProfileSmooth := by
  intro ν c hν hc tr hb
  -- (1) profile form of the stream, rewritten in train variables `(s, (q, η))`
  have hψ : ContDiffOn ℝ ∞ (trainProfile tr.ψ) {x : ProfilePoint | 0 < x.2.2} :=
    (hS ν c hν hc tr hb).1
  have hg : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => (x.2.1, (x.2.2, x.1))) := by
    fun_prop
  have hmap : MapsTo (fun x : ℝ × (ℝ × ℝ) => (x.2.1, (x.2.2, x.1)))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) {x : ProfilePoint | 0 < x.2.2} := by
    intro x hx
    exact hx.1
  have hψS : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hψ.comp hg.contDiffOn hmap
  -- (2) smoothness of the horizontal average `(s, η) ↦ hmean c (tr.ψ s) η`, i.e. of `meanStream`
  have hmeanS := hH c hc tr.ψ hψS
  -- (3) profile form of the mean stream
  have hS' : ContDiffOn ℝ ∞
      (trainProfile fun s z => UnforcedLeray.Short.PartI.meanStream tr s z.2)
      {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_trainProfile_of_eta (G := UnforcedLeray.Short.PartI.meanStream tr) hmeanS
  -- (4) the profile of a pointwise difference is the difference of the profiles
  have heq : trainProfile (fun s z => tr.ψ s z - UnforcedLeray.Short.PartI.meanStream tr s z.2)
      = fun y => trainProfile tr.ψ y
          - trainProfile (fun s z => UnforcedLeray.Short.PartI.meanStream tr s z.2) y :=
    rfl
  rw [heq]
  exact hψ.sub hS'

end UnforcedLeray.Short.PartIIa
