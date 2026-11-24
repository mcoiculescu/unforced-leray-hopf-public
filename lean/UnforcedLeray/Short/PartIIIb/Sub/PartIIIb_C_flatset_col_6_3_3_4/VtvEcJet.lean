import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4.IterDerivBound

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The second derivative in direction `u` of a vector field, bounded by the operator norm of
the second derivative. -/
theorem norm_fderiv_apply_le_iter {g : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} (hg : ContDiff ℝ ∞ g) (x u d : ℝ × ℝ)
    (hu : ‖u‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
    ‖fderiv ℝ (fun z => fderiv ℝ g z u) x d‖ ≤ ‖iteratedFDeriv ℝ 2 g x‖ := by
  have h := norm_fderiv_iteratedFDeriv_apply_le hg 1 x d ![u] hd
    (by intro i; fin_cases i; simpa using hu)
  have hfun : (fun z => iteratedFDeriv ℝ 1 g z ![u]) = fun z => fderiv ℝ g z u := by
    funext z
    simp [iteratedFDeriv_one_apply]
  rw [hfun] at h
  exact h

theorem vtvEcJet : VtvEcJet := by
  intro ν c tr hBUC s₁ s₂ hs₁
  obtain ⟨M, hM⟩ := UnforcedLeray.Short.PartI.IsBUCTrain.deriv_bound hBUC
    (le_max_right s₂ 0) 2
  refine ⟨2 * |M|, ?_⟩
  intro s hs x j
  have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
  have hsS : s ∈ Icc (0 : ℝ) (max s₂ 0) := ⟨hs0.le, hs.2.trans (le_max_left _ _)⟩
  have hv : ContDiff ℝ ∞ (fun y : ℝ × ℝ => tr.v s y) := by
    have h1 : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.mono (prod_mono (Ioi_subset_Ici le_rfl) subset_rfl)
    have hpair : ContDiff ℝ ∞ (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ))) :=
      contDiff_const.prodMk contDiff_id
    have hmem : ∀ y : ℝ × ℝ, ((s, y) : ℝ × (ℝ × ℝ)) ∈ Ioi 0 ×ˢ (univ : Set (ℝ × ℝ)) := fun y =>
      ⟨hs0, mem_univ _⟩
    exact h1.comp_contDiff hpair hmem
  -- the coordinate derivatives of the velocity
  have hEc : UnforcedLeray.B0238.Ec tr s = fun z =>
      fderiv ℝ (tr.v s) z (1, 0) 1 - fderiv ℝ (tr.v s) z (0, 1) 0 := by
    funext z
    have hv_at : HasFDerivAt (tr.v s) (fderiv ℝ (tr.v s) z) z :=
      ((hv.differentiable (by simp)) z).hasFDerivAt
    have hq : deriv (fun q : ℝ => tr.v s (q, z.2) 1) z.1 = fderiv ℝ (tr.v s) z (1, 0) 1 := by
      have hline : HasDerivAt (fun q : ℝ => ((q, z.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) z.1 :=
        (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
      have hco := hv_at.comp_hasDerivAt z.1 hline
      have hpr := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.comp_hasDerivAt z.1 hco
      exact hpr.deriv
    have hη : deriv (fun η : ℝ => tr.v s (z.1, η) 0) z.2 = fderiv ℝ (tr.v s) z (0, 1) 0 := by
      have hline : HasDerivAt (fun η : ℝ => ((z.1, η) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) z.2 :=
        (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
      have hco := hv_at.comp_hasDerivAt z.2 hline
      have hpr := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.comp_hasDerivAt z.2 hco
      exact hpr.deriv
    unfold UnforcedLeray.B0238.Ec
    unfold Cyl.curl Cyl.partialQ Cyl.partialEta
    rw [hq, hη]
  have hG1 : HasFDerivAt (fun z => fderiv ℝ (tr.v s) z (1, 0))
      (fderiv ℝ (fun z => fderiv ℝ (tr.v s) z (1, 0)) x) x := by
    have hC : ContDiff ℝ ∞ (fun z => fderiv ℝ (tr.v s) z (1, 0)) :=
      (hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact (hC.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hG2 : HasFDerivAt (fun z => fderiv ℝ (tr.v s) z (0, 1))
      (fderiv ℝ (fun z => fderiv ℝ (tr.v s) z (0, 1)) x) x := by
    have hC : ContDiff ℝ ∞ (fun z => fderiv ℝ (tr.v s) z (0, 1)) :=
      (hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact (hC.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hF1 : HasFDerivAt (fun z => fderiv ℝ (tr.v s) z (1, 0) 1)
      ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).comp
        (fderiv ℝ (fun z => fderiv ℝ (tr.v s) z (1, 0)) x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.comp x hG1
  have hF2 : HasFDerivAt (fun z => fderiv ℝ (tr.v s) z (0, 1) 0)
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).comp
        (fderiv ℝ (fun z => fderiv ℝ (tr.v s) z (0, 1)) x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.comp x hG2
  have hdiff : HasFDerivAt (fun z => fderiv ℝ (tr.v s) z (1, 0) 1 - fderiv ℝ (tr.v s) z (0, 1) 0)
      ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).comp
          (fderiv ℝ (fun z => fderiv ℝ (tr.v s) z (1, 0)) x) -
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).comp
          (fderiv ℝ (fun z => fderiv ℝ (tr.v s) z (0, 1)) x)) x := hF1.sub hF2
  have hpd : B0579.pd j (UnforcedLeray.B0238.Ec tr s) x =
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2))
        (fderiv ℝ (fun z => fderiv ℝ (tr.v s) z (1, 0)) x (B0579.dir j)) -
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))
        (fderiv ℝ (fun z => fderiv ℝ (tr.v s) z (0, 1)) x (B0579.dir j)) := by
    rw [hEc]
    unfold B0579.pd
    rw [hdiff.fderiv]
    simp only [sub_apply, ContinuousLinearMap.comp_apply]
  have hd : ‖B0579.dir j‖ ≤ 1 := by
    fin_cases j <;> simp [B0579.dir, Prod.norm_def]
  have hu1 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  have hu2 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  have hK1 : ‖fderiv ℝ (fun z => fderiv ℝ (tr.v s) z (1, 0)) x (B0579.dir j)‖ ≤ M :=
    (norm_fderiv_apply_le_iter hv x (1, 0) (B0579.dir j) hu1 hd).trans (hM s hsS x)
  have hK2 : ‖fderiv ℝ (fun z => fderiv ℝ (tr.v s) z (0, 1)) x (B0579.dir j)‖ ≤ M :=
    (norm_fderiv_apply_le_iter hv x (0, 1) (B0579.dir j) hu2 hd).trans (hM s hsS x)
  have hcoord : ∀ (w : EuclideanSpace ℝ (Fin 2)) (i : Fin 2),
      |(EuclideanSpace.proj (𝕜 := ℝ) i) w| ≤ ‖w‖ := fun w i => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w i
  rw [hpd]
  have h1 := (hcoord (fderiv ℝ (fun z => fderiv ℝ (tr.v s) z (1, 0)) x (B0579.dir j)) 1).trans hK1
  have h2 := (hcoord (fderiv ℝ (fun z => fderiv ℝ (tr.v s) z (0, 1)) x (B0579.dir j)) 0).trans hK2
  have h3 := abs_sub
    ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2))
        (fderiv ℝ (fun z => fderiv ℝ (tr.v s) z (1, 0)) x (B0579.dir j)))
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))
        (fderiv ℝ (fun z => fderiv ℝ (tr.v s) z (0, 1)) x (B0579.dir j)))
  linarith [le_abs_self M]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
