import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ForceMemX

/-!
# Part III-a: joint continuity of `∇E` (helper of `adjWRateCont`, global leaf)

`(r, x) ↦ ∂_j E(r, x)` is jointly continuous on `(0, ∞) × ℝ²` since the train velocity is jointly
smooth on `[0, ∞) × ℝ²` (`TrainSol.isTrain.smooth_v`) and `∂_j E = ∂_j(∂_q v₂ - ∂_η v₁)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace GlobEAux

/-- The slice derivative of a function that is smooth on the open strip `(0,∞) × ℝ²`. -/
lemma pd_slice {F : ℝ × (ℝ × ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) {r : ℝ} (hr : 0 < r)
    (k : Fin 2) (x : ℝ × ℝ) :
    B0579.pd k (fun y => F (r, y)) x = fderiv ℝ F (r, x) ((0 : ℝ), B0579.dir k) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hd : DifferentiableAt ℝ F (r, x) :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds ⟨hr, mem_univ _⟩)
  have hinj : HasFDerivAt (fun y : ℝ × ℝ => ((r, y) : ℝ × (ℝ × ℝ)))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
    (hasFDerivAt_const (𝕜 := ℝ) r x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
  have := (hd.hasFDerivAt.comp x hinj).fderiv
  unfold B0579.pd
  rw [show (fun y => F (r, y)) = F ∘ (fun y : ℝ × ℝ => ((r, y) : ℝ × (ℝ × ℝ))) from rfl, this]
  simp

lemma contOn_pd_pd {F : ℝ × (ℝ × ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) (j k : Fin 2) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (B0579.pd k (fun y => F (p.1, y))) p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hG : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p ((0 : ℝ), B0579.dir k))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (hF.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const
  have hH : ContinuousOn (fun p => fderiv ℝ (fun q => fderiv ℝ F q ((0 : ℝ), B0579.dir k)) p
      ((0 : ℝ), B0579.dir j)) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    ((hG.fderiv_of_isOpen (m := ∞) hU (by simp)).continuousOn).clm_apply continuousOn_const
  refine hH.congr fun p hp => ?_
  have hp1 : 0 < p.1 := hp.1
  have h1 : B0579.pd k (fun y => F (p.1, y)) = fun y => fderiv ℝ F (p.1, y) ((0 : ℝ), B0579.dir k) :=
    funext fun y => pd_slice hF hp1 k y
  rw [h1]
  have := pd_slice (F := fun q => fderiv ℝ F q ((0 : ℝ), B0579.dir k)) hG hp1 j p.2
  simpa using this

lemma contOn_pd_Ec {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (j : Fin 2) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (UnforcedLeray.B0238.Ec tr p.1) p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
  have hS : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self subset_rfl)
  have hF : ∀ i : Fin 2, ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 i)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn hS
  have h := (contOn_pd_pd (hF 1) j 0).sub (contOn_pd_pd (hF 0) j 1)
  refine h.congr fun p hp => ?_
  have hp0 : 0 ≤ p.1 := hp.1.le
  have hv : ContDiff ℝ ∞ (tr.v p.1) := UnforcedLeray.B0238.contDiff_Vc tr hp0
  have hv1 : ContDiff ℝ 1 (tr.v p.1) := hv.of_le (by simp)
  have hf1 : ContDiff ℝ ∞ (fun w => tr.v p.1 w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have hf0 : ContDiff ℝ ∞ (fun w => tr.v p.1 w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have hfun : UnforcedLeray.B0238.Ec tr p.1
      = fun z => B0579.pd 0 (fun w => tr.v p.1 w 1) z - B0579.pd 1 (fun w => tr.v p.1 w 0) z := by
    funext z
    unfold UnforcedLeray.B0238.Ec
    rw [UnforcedLeray.B0238.curl_eq_fderiv hv1 z]
    simp [B0579.pd, B0579.dir]
  show B0579.pd j (UnforcedLeray.B0238.Ec tr p.1) p.2 = _
  rw [hfun]
  have hd1 : DifferentiableAt ℝ (B0579.pd 0 (fun w => tr.v p.1 w 1)) p.2 :=
    (ForceMemXAux.contDiff_pd hf1 0).differentiable (by simp) _
  have hd0 : DifferentiableAt ℝ (B0579.pd 1 (fun w => tr.v p.1 w 0)) p.2 :=
    (ForceMemXAux.contDiff_pd hf0 1).differentiable (by simp) _
  unfold B0579.pd at hd1 hd0 ⊢
  rw [fderiv_fun_sub hd1 hd0]
  simp

end GlobEAux

end UnforcedLeray.Short.IIIa
