import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.SliceJetBounds

/-!
# `PartIII-a:T21/2/7/2/1/1/6/22`: the velocity jets are smooth coefficients (`TrainVCoeff`)

Source: `the November 2 reference manuscript` lines 270-288, 2866-2870.
Route: `sliceJetBounds` applied to the component `(r, x) ↦ v_l(r, x)`, with the weight `1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The component `v_l` as a jointly smooth function of (age, position) on `(0, ∞) × ℝ²`. -/
theorem trainVC_contDiffOn (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (l : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 l)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
  have hU : Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    prod_mono Ioi_subset_Ici_self (subset_univ _)
  exact (EuclideanSpace.proj (𝕜 := ℝ) l).contDiff.comp_contDiffOn (tr.isTrain.smooth_v.mono hU)

/-- The age-jet bound: the component of the joint derivative is bounded by the norm of the
joint derivative of the velocity, on `(0, S) × ℝ²`. -/
theorem trainVC_norm_le (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (l : Fin 2) (n : ℕ)
    (S C : ℝ)
    (hC : ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
      ‖iteratedFDerivWithin ℝ n (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ ≤ C)
    (ρ : ℝ) (hρ : ρ ∈ Ioo (0 : ℝ) S) (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ n (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 l) (ρ, x)‖ ≤
      ‖(EuclideanSpace.proj (𝕜 := ℝ) l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ * C := by
  have hUS : Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    prod_mono Ioi_subset_Ici_self (subset_univ _)
  have hUo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : (ρ, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hρ.1, mem_univ _⟩
  have hf : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2)
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := tr.isTrain.smooth_v
  have hfU : ContDiffWithinAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x) :=
    (hf.mono hUS).contDiffWithinAt hmem
  have h1 : iteratedFDeriv ℝ n (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 l) (ρ, x)
      = iteratedFDerivWithin ℝ n (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 l)
          (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x) :=
    (iteratedFDerivWithin_of_isOpen n hUo hmem).symm
  have h2 : ‖iteratedFDerivWithin ℝ n (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 l)
        (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ ≤
      ‖(EuclideanSpace.proj (𝕜 := ℝ) l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ *
        ‖iteratedFDerivWithin ℝ n (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2)
          (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ :=
    (EuclideanSpace.proj (𝕜 := ℝ) l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).norm_iteratedFDerivWithin_comp_left
      hfU hUo.uniqueDiffOn hmem (by exact_mod_cast le_top)
  have h3 : iteratedFDerivWithin ℝ n (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2)
        (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)
      = iteratedFDerivWithin ℝ n (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2)
          (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x) := by
    have := iteratedFDerivWithin_inter_open (𝕜 := ℝ)
      (f := fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (s := Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))
      (n := n) hUo hmem
    rwa [inter_eq_right.2 hUS] at this
  have h4 := hC ρ ⟨hρ.1.le, hρ.2.le⟩ x
  rw [h1]
  calc _ ≤ _ := h2
    _ = _ := by rw [h3]
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)

/-- **The velocity jets are smooth coefficients** (SP 270-288; `TrainSTJets`). -/
theorem trainVCoeff (m : ℝ) : TrainVCoeff m := by
  unfold TrainVCoeff
  intro ν hν0 hν1 tr hST a b ha i l
  have hVb : ∀ (n : ℕ) (S : ℝ), ∃ C : ℝ, ∀ ρ ∈ Ioo (0 : ℝ) S, ∀ x : ℝ × ℝ,
      (fun _ : ℝ × ℝ => (1 : ℝ)) x *
        ‖iteratedFDeriv ℝ n (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 l) (ρ, x)‖ ≤ C := by
    intro n S
    obtain ⟨C, hC⟩ := hST (max S 0) (le_max_right S 0) n
    refine ⟨‖(EuclideanSpace.proj (𝕜 := ℝ) l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ * C,
      fun ρ hρ x => ?_⟩
    have hρS : ρ ∈ Ioo (0 : ℝ) (max S 0) := ⟨hρ.1, hρ.2.trans_le (le_max_left S 0)⟩
    have := trainVC_norm_le ν _ tr l n (max S 0) C (fun ρ hρ x => (hC ρ hρ x).1) ρ hρS x
    simpa only [one_mul] using this
  have key := sliceJetBounds (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 l) (fun _ => (1 : ℝ))
    (fun _ => one_pos) (trainVC_contDiffOn ν _ tr l) hVb a b ha i
  have hper : ∀ r ∈ Ioo a b, ∀ x : ℝ × ℝ,
      vJet tr i r (x.1 + ν ^ (-2 : ℝ), x.2) l = vJet tr i r x l := by
    intro r hr x
    have hr0 : 0 < r := lt_of_le_of_lt ha hr.1
    unfold vJet
    apply Filter.EventuallyEq.iteratedDeriv_eq
    filter_upwards [Ioi_mem_nhds hr0] with ρ hρ
    have hp := tr.isTrain.periodic_v ρ (le_of_lt hρ) x
    simp only [hp]
  refine ⟨⟨fun r hr => ⟨key.1 r hr, fun x => hper r hr x⟩, fun w r hr => ?_⟩, key.2.2⟩
  have hk := key.2.1 w r hr
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC⟩ := hk.1
    exact ⟨C, fun x => by simpa only [one_mul, vJet] using hC x⟩
  · intro ε hε
    filter_upwards [hk.2 ε hε] with r' hr' x
    simpa only [one_mul, vJet] using hr' x

end UnforcedLeray.Short.IIIa
