import UnforcedLeray.Short.PartIIb.Sub.T22_1_1

/-!
# Part II-b, task `PartII-b:T22/1/1/1`: the regularity leaf `TcRegular`

Source: `IsTrain.smooth_v` on `Ici 0 ×ˢ univ` (`Units/B0140.lean`), with the slice direction
tangent to the product set, so `fderiv ℝ (v σ) x = fderivWithin (v) (Ici 0 ×ˢ univ) (σ,x) ∘ inr`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.CylPDE

theorem tcRegular : UnforcedLeray.Short.IIb.CylPDE.TcRegular := by
  intro ν c tr T hT
  set S : Set (ℝ × Pl) := Ici 0 ×ˢ univ with hS
  have hSU : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hF : ContDiffOn ℝ ∞ (fun x : ℝ × Pl => tr.v x.1 x.2) S := tr.isTrain.smooth_v
  have hF1 : ContDiffOn ℝ 1 (fun x : ℝ × Pl => tr.v x.1 x.2) S := hF.of_le (by norm_num)
  have hslice : ∀ σ : ℝ, 0 ≤ σ → ∀ x : Pl,
      HasFDerivAt (tr.v σ)
        ((fderivWithin ℝ (fun z : ℝ × Pl => tr.v z.1 z.2) S (σ, x)).comp
          (ContinuousLinearMap.inr ℝ ℝ Pl)) x := by
    intro σ hσ x
    have hdiff : DifferentiableWithinAt ℝ (fun z : ℝ × Pl => tr.v z.1 z.2) S (σ, x) :=
      (hF1.differentiableOn one_ne_zero) (σ, x) ⟨hσ, mem_univ _⟩
    have hFD := hdiff.hasFDerivWithinAt
    have hφ : HasFDerivAt (fun y : Pl => ((σ, y) : ℝ × Pl))
        (ContinuousLinearMap.inr ℝ ℝ Pl) x := by
      have hc0 : HasFDerivAt (fun _ : Pl => σ) (0 : Pl →L[ℝ] ℝ) x := hasFDerivAt_const σ x
      have hi : HasFDerivAt (fun y : Pl => y) (ContinuousLinearMap.id ℝ Pl) x := hasFDerivAt_id x
      have h0 := hc0.prodMk hi
      have hE : (ContinuousLinearMap.prod (0 : Pl →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ Pl)) =
          ContinuousLinearMap.inr ℝ ℝ Pl :=
        ContinuousLinearMap.ext fun v => by simp
      rw [hE] at h0
      exact h0
    have hmaps : MapsTo (fun y : Pl => ((σ, y) : ℝ × Pl)) univ S :=
      fun y _ => ⟨hσ, mem_univ _⟩
    have hc := hFD.comp x hφ.hasFDerivWithinAt hmaps
    rw [hasFDerivWithinAt_univ] at hc
    exact hc
  have hcont : ContinuousOn (fun z : ℝ × Pl => fderiv ℝ (tr.v z.1) z.2) S := by
    have hD : ContinuousOn (fun z : ℝ × Pl =>
        (fderivWithin ℝ (fun z : ℝ × Pl => tr.v z.1 z.2) S z).comp
          (ContinuousLinearMap.inr ℝ ℝ Pl)) S :=
      (hF1.continuousOn_fderivWithin hSU le_rfl).clm_comp continuousOn_const
    refine hD.congr ?_
    rintro ⟨σ, x⟩ ⟨hσ, _⟩
    exact (hslice σ hσ x).fderiv
  have hsub : Icc (0 : ℝ) T ×ˢ (univ : Set Pl) ⊆ S :=
    Set.prod_mono Icc_subset_Ici_self (subset_refl _)
  refine ⟨?_, ?_, ?_⟩
  · intro σ hσ
    have hf : ContDiff ℝ 1 (fun y : Pl => ((σ, y) : ℝ × Pl)) :=
      contDiff_const.prodMk contDiff_id
    have hmaps : MapsTo (fun y : Pl => ((σ, y) : ℝ × Pl)) univ S :=
      fun y _ => ⟨hσ.1, mem_univ _⟩
    have h := hF1.comp hf.contDiffOn hmaps
    exact contDiffOn_univ.mp h
  · exact hF.continuousOn.mono hsub
  · exact hcont.mono hsub

end UnforcedLeray.Short.IIb.CylPDE
