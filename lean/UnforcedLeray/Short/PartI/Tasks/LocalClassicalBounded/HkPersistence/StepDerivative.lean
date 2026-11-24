import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.StepDerivative.Core
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.BaseDerivative

/-!
# Part I, task `PartI:T02/1/2/5`: `StepDerivative`

Source of record: `the November 2 reference manuscript`, lines 261-288.
Assembly from `linearPicardCore` (existence of the derivative path of the linear solution `w`),
the product rule `bilDuhamelDerivative` and uniqueness of derivative paths.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.TrainB

/-- **Task `PartI:T02/1/2/5`: `StepDerivative`.** -/
theorem stepDerivative : StepDerivative := by
  intro ν c T hν hc hc1 hT j u u' h h' w hu hh hw
  obtain ⟨C₀, hC₀, hWl, hWr⟩ := bilWeightedEstimate ν c hν hc hc1
  have hP := bilDuhamelDerivative ν c T hν hc hc1 hT j
  have hA := bilDuhamelAdditive ν c T hν hc hc1 hT
  have hw0 : w = h + (bilDuhamel hc hc1 hν hT.le u w + bilDuhamel hc hc1 hν hT.le w u) := hw
  obtain ⟨d, hd⟩ := linearPicardCore j (fun a b => bilDuhamel hc hc1 hν hT.le a b)
    (fun a a' b => (hA a a' b b).1) (fun a b b' => (hA a a b b').2)
    (fun a a' b b' ha hb => hP a a' b b' ha hb) C₀ hC₀ (hWl T hT) (hWr T hT)
    (fun a a' x d h1 h2 h3 => derivClosed c T j a a' x d h1 h2 h3)
    u u' h h' w hu hh hw0
  refine ⟨d, hd, ?_⟩
  have h1 := hP u u' w d hu hd
  have h2 := hP w d u u' hd hu
  have h3 := hh.add (h1.add h2)
  rw [← hw0] at h3
  have h4 := hd.unique h3
  unfold linDuhamel
  generalize bilDuhamel hc hc1 hν hT.le u' w = p1 at h4 ⊢
  generalize bilDuhamel hc hc1 hν hT.le u d = p2 at h4 ⊢
  generalize bilDuhamel hc hc1 hν hT.le d u = p3 at h4 ⊢
  generalize bilDuhamel hc hc1 hν hT.le w u' = p4 at h4 ⊢
  rw [h4]
  abel
end UnforcedLeray.Short.PartI
