import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Sub.PartIIIa_T21_2_7_2_1_2_1_3

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjSpatial_contDiff_ha0 (w : List (Fin 2)) (g : ℝ × ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (adjSpatial w g) := by
  induction w with
  | nil => exact hg
  | cons k w ih =>
    show ContDiff ℝ ∞ (fun y => fderiv ℝ (adjSpatial w g) y (B0579.dir k))
    exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem stPartialSmooth : UnforcedLeray.Short.IIIa.StPartialSmooth := by
  intro φ' t s hsm j w r hr
  have hU : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
  have key : ∀ n : ℕ, ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => iteratedDeriv n (fun r' => φ' r' p.2) p.1) (Ioo t s ×ˢ univ) := by
    intro n
    induction n with
    | zero => simpa [iteratedDeriv_zero] using hsm
    | succ n ih =>
      have hfd := ih.fderiv_of_isOpen hU (m := ∞) (by simp)
      refine ContDiffOn.congr (f := fun p : ℝ × (ℝ × ℝ) =>
        fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => iteratedDeriv n (fun r' => φ' r' q.2) q.1) p
          ((1 : ℝ), (0 : ℝ × ℝ))) ?_ ?_
      · exact hfd.clm_apply contDiffOn_const
      · rintro ⟨r0, y⟩ hp
        have hp' : (r0, y) ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) := hp
        have hdiff : DifferentiableAt ℝ
            (fun q : ℝ × (ℝ × ℝ) => iteratedDeriv n (fun r' => φ' r' q.2) q.1) (r0, y) :=
          (ih.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp')
        have hline : HasDerivAt (fun r' : ℝ => ((r', y) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) r0 :=
          (hasDerivAt_id r0).prodMk (hasDerivAt_const r0 y)
        have hd := hdiff.hasFDerivAt.comp_hasDerivAt r0 hline
        show iteratedDeriv (n + 1) (fun r' => φ' r' y) r0 = _
        rw [iteratedDeriv_succ]
        exact hd.deriv
  have hslice : ContDiff ℝ ∞ (fun y => iteratedDeriv j (fun r' => φ' r' y) r) := by
    have hy : ContDiffOn ℝ ∞ (fun y : ℝ × ℝ => ((r, y) : ℝ × (ℝ × ℝ))) univ :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    have h1 := (key j).comp hy
      (fun y _ => (⟨hr, mem_univ y⟩ : (r, y) ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ))))
    exact contDiffOn_univ.mp h1
  show ContDiff ℝ ∞ (adjSpatial w (fun y => iteratedDeriv j (fun r' => φ' r' y) r))
  exact adjSpatial_contDiff_ha0 w _ hslice

end UnforcedLeray.Short.IIIa
