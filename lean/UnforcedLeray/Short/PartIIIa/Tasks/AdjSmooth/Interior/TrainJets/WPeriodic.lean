import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `PartIII-a:T21/2/7/2/1/1/2/14`: words of a periodic field are periodic (`TjWPeriodic`). -/
theorem tjWPeriodic : TjWPeriodic := by
  intro c h hh hper
  obtain ⟨k, hk⟩ : ∃ k : ℝ × (ℝ × ℝ), k = (0, (c, 0)) := ⟨_, rfl⟩
  have hpk : ∀ p : ℝ × (ℝ × ℝ), p + k = (p.1, (p.2.1 + c, p.2.2)) := by
    intro p
    simp [hk, Prod.ext_iff]
  have hmaps : ∀ p ∈ tjU, p + k ∈ tjU := by
    intro p hp
    refine ⟨?_, mem_univ _⟩
    have h1 : (p + k).1 = p.1 := by simp [hk]
    show (0 : ℝ) ≤ (p + k).1
    rw [h1]
    exact hp.1
  have hA : ∀ L : List (Fin 3), ∀ p ∈ tjU, tjW L h (p + k) = tjW L h p := by
    intro L
    induction L with
    | nil =>
      intro p hp
      simp only [tjW_nil]
      rw [hpk p]
      exact hper p.1 hp.1 p.2
    | cons a L ih =>
      intro p hp
      have hG : ContDiffOn ℝ ∞ (tjW L h) tjU := tjW_contDiffOn hh L
      have hd : DifferentiableWithinAt ℝ (tjW L h) tjU (p + k) :=
        (hG.differentiableOn (by simp)) _ (hmaps p hp)
      have hTd : HasFDerivAt (fun q : ℝ × (ℝ × ℝ) => q + k) (ContinuousLinearMap.id ℝ _) p :=
        (hasFDerivAt_id p).add_const k
      have hcomp : HasFDerivWithinAt ((tjW L h) ∘ (fun q => q + k))
          ((fderivWithin ℝ (tjW L h) tjU (p + k)).comp (ContinuousLinearMap.id ℝ _)) tjU p :=
        HasFDerivWithinAt.comp p hd.hasFDerivWithinAt hTd.hasFDerivWithinAt
          (fun q hq => hmaps q hq)
      have hcomp' := hcomp.fderivWithin (uniqueDiffOn_tjU p hp)
      have hcongr : fderivWithin ℝ ((tjW L h) ∘ (fun q => q + k)) tjU p =
          fderivWithin ℝ (tjW L h) tjU p :=
        fderivWithin_congr (fun q hq => ih q hq) (ih p hp)
      have hD : fderivWithin ℝ (tjW L h) tjU p = fderivWithin ℝ (tjW L h) tjU (p + k) := by
        rw [← hcongr, hcomp', ContinuousLinearMap.comp_id]
      simp only [tjW_cons]
      rw [hD]
  intro L ρ hρ x
  have := hA L (ρ, x) ⟨hρ, mem_univ _⟩
  rw [hpk] at this
  exact this

end UnforcedLeray.Short.IIIa
