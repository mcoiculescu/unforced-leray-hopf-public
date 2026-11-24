import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4_1

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open scoped ContDiff

theorem compSmoothLeaf : CompSmoothLeaf := by
  intro c M hM
  have hk : ∀ k : Fin 4,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (tv4 (M x) k).re) := by
    intro k
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => tv4 (M x) k) :=
      ((EuclideanSpace.proj k : EuclideanSpace ℂ (Fin 4) →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp
        hM.smooth
    exact Complex.reCLM.contDiff.comp h1
  have hper : ∀ s q η : ℝ, tv4 (M (s, (q + c, η))) = tv4 (M (s, (q, η))) :=
    fun s q η => hM.periodic (s, (q, η))
  have hA : cmpA M = fun x => (tv4 (M x) 0).re := by
    funext x; simp [cmpA, tv4]
  have hB : cmpB M = fun x => (tv4 (M x) 1).re := by
    funext x; simp [cmpB, tv4]
  have hC : cmpC M = fun x => (tv4 (M x) 2).re := by
    funext x; simp [cmpC, tv4]
  have hD : cmpD M = fun x => (tv4 (M x) 3).re := by
    funext x; simp [cmpD, tv4]
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · rw [hA]
    exact ⟨hk 0, fun s q η => by
      show (tv4 (M (s, (q + c, η))) 0).re = (tv4 (M (s, (q, η))) 0).re
      rw [hper s q η]⟩
  · rw [hB]
    exact ⟨hk 1, fun s q η => by
      show (tv4 (M (s, (q + c, η))) 1).re = (tv4 (M (s, (q, η))) 1).re
      rw [hper s q η]⟩
  · rw [hC]
    exact ⟨hk 2, fun s q η => by
      show (tv4 (M (s, (q + c, η))) 2).re = (tv4 (M (s, (q, η))) 2).re
      rw [hper s q η]⟩
  · rw [hD]
    exact ⟨hk 3, fun s q η => by
      show (tv4 (M (s, (q + c, η))) 3).re = (tv4 (M (s, (q, η))) 3).re
      rw [hper s q η]⟩

end UnforcedLeray.Short.PartIIIb.NearInst
