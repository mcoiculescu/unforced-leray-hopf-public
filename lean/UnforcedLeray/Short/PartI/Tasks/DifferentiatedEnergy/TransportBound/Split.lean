import UnforcedLeray.Short.PartI.Sub.PartI_T08_7
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

theorem jetSplit_proof : UnforcedLeray.Short.PartI.JetSplit := by
  intro c j f g₁ g₂ hg₁ hg₂ hI₁ hI₂
  have hcomp : ∀ (g : Plane → Vec), ContDiff ℝ ∞ g → ∀ k : Fin 2,
      ContDiff ℝ ∞ (fun x => g x k) := by
    intro g hg k
    exact (EuclideanSpace.proj k).contDiff.comp hg
  have hadd : ∀ (w : List Bool) (k : Fin 2) (z : Plane),
      wordComp w (fun x => g₁ x + g₂ x) k z = wordComp w g₁ k z + wordComp w g₂ k z := by
    intro w k z
    have h := ForcingIBP.derivWord_add_smooth w (fun x => g₁ x k) (fun x => g₂ x k)
      (hcomp g₁ hg₁ k) (hcomp g₂ hg₂ k)
    unfold wordComp
    have e : (fun x => (g₁ x + g₂ x) k) = fun x => g₁ x k + g₂ x k := rfl
    rw [e, h]
  have key : ∀ z : Plane,
      (∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        wordComp w f k z * wordComp w (fun x => g₁ x + g₂ x) k z) =
      (∑ w ∈ wordsOfLength j, ∑ k : Fin 2, wordComp w f k z * wordComp w g₁ k z) +
      (∑ w ∈ wordsOfLength j, ∑ k : Fin 2, wordComp w f k z * wordComp w g₂ k z) := by
    intro z
    simp only [hadd, mul_add, Finset.sum_add_distrib]
  unfold jetPair
  simp only [key]
  exact integral_add hI₁ hI₂

end UnforcedLeray.Short.PartI
