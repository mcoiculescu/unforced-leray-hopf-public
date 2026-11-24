import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.TimeJetsEnd.trainVCoeffW.SliceJetBoundsW

/-!
# `PartIII-a:T21/2/7/2/1/2/1/2/6`: the one-sided velocity jets are smooth coefficients on `[a, b)`

Source: `the November 2 reference manuscript` lines 270-288, 3052-3061.
Route: `sliceJetBoundsW` (one-sided age jets, valid at the age `0`) applied to the component
`(r, x) ↦ v_l(r, x)` with the weight `1`; the bound is `TrainSTJets`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **The one-sided velocity jets are smooth coefficients on `[a, b)`** (SP 270-288, 3060). -/
theorem trainVCoeffW : ∀ m : ℝ, TrainVCoeffW m := by
  intro m
  unfold TrainVCoeffW
  intro ν hν0 hν1 tr hST a b ha i l
  have hVb : ∀ (n : ℕ) (S : ℝ), ∃ C : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
      (fun _ : ℝ × ℝ => (1 : ℝ)) x *
        ‖iteratedFDerivWithin ℝ n (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 l)
          (Ici 0 ×ˢ univ) (ρ, x)‖ ≤ C := by
    intro n S
    obtain ⟨C, hC⟩ := hST (max S 0) (le_max_right S 0) n
    refine ⟨‖(EuclideanSpace.proj (𝕜 := ℝ) l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ * C,
      fun ρ hρ x => ?_⟩
    have hρ' : ρ ∈ Icc (0 : ℝ) (max S 0) := ⟨hρ.1, hρ.2.trans (le_max_left S 0)⟩
    have h := (EuclideanSpace.proj (𝕜 := ℝ) l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).norm_iteratedFDerivWithin_comp_left
      (tr.isTrain.smooth_v (ρ, x) ⟨hρ.1, mem_univ x⟩) PdEc.strip_uniqueDiff
      ⟨hρ.1, mem_univ x⟩ (by exact_mod_cast le_top) (n := n)
    simp only [one_mul]
    exact h.trans (mul_le_mul_of_nonneg_left (hC ρ hρ' x).1 (norm_nonneg _))
  have key := sliceJetBoundsW (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 l) (fun _ => (1 : ℝ))
    (fun _ => one_pos) (PdEc.wComp_contDiffOn tr l) hVb a b ha i
  have hper : ∀ r ∈ Ico a b, ∀ x : ℝ × ℝ,
      vJetW tr i r (x.1 + ν ^ (-2 : ℝ), x.2) l = vJetW tr i r x l := by
    intro r hr x
    unfold vJetW
    refine iteratedDerivWithin_congr (fun ρ hρ => ?_) (show r ∈ Ici (0 : ℝ) from ha.trans hr.1)
    have hp := tr.isTrain.periodic_v ρ hρ x
    simp only [hp]
  refine ⟨⟨fun r hr => ⟨key.1 r hr, fun x => hper r hr x⟩, fun w r hr => ?_⟩, key.2.2⟩
  have hk := key.2.1 w r hr
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC⟩ := hk.1
    exact ⟨C, fun x => by
      have h := hC x
      simp only [one_mul] at h
      exact h⟩
  · intro ε hε
    filter_upwards [hk.2 ε hε] with r' hr' x
    have h := hr' x
    simp only [one_mul] at h
    exact h

end UnforcedLeray.Short.IIIa
