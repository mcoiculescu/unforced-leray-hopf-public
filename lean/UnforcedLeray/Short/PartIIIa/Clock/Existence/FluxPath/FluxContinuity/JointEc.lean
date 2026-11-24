import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.GCont_3

/-!
# Joint continuity of the train vorticity `Ec` on `[0, ∞) × ℝ²` (SP 2819-2836)

Same mechanism as `train_joint_cont` (`Sub/T21_2_3/.../GCont_3.lean`): on `[0,∞)` the vorticity is
a combination of within-`S` first derivatives of the jointly `C^∞` velocity components, hence
jointly continuous.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa.GCont3Aux

theorem jointContinuousOn_Ec {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) :
    ContinuousOn (fun p : ℝ × UnforcedLeray.Cyl.Plane => UnforcedLeray.B0238.Ec tr p.1 p.2)
      (Set.Ici 0 ×ˢ Set.univ) := by
  have hS : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) Sx := tr.isTrain.smooth_v
  have hG : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 j) Sx := fun j =>
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn hS
  have hEc : ∀ t : ℝ, 0 ≤ t → ∀ z : ℝ × ℝ, UnforcedLeray.B0238.Ec tr t z =
      fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1) Sx (t, z) (0, (1, 0)) -
        fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0) Sx (t, z) (0, (0, 1)) := by
    intro t ht z
    have hv : ContDiff ℝ ∞ (tr.v t) := UnforcedLeray.B0238.contDiff_Vc tr ht
    have hv1 : ContDiff ℝ 1 (tr.v t) := hv.of_le (by simp)
    have e1 : fderiv ℝ (fun w : ℝ × ℝ => tr.v t w 1) z (1, 0) =
        fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1) Sx (t, z) (0, (1, 0)) :=
      fderiv_slice_apply ((hG 1).of_le (by simp)) ht z (1, 0)
    have e0 : fderiv ℝ (fun w : ℝ × ℝ => tr.v t w 0) z (0, 1) =
        fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0) Sx (t, z) (0, (0, 1)) :=
      fderiv_slice_apply ((hG 0).of_le (by simp)) ht z (0, 1)
    unfold UnforcedLeray.B0238.Ec
    rw [UnforcedLeray.B0238.curl_eq_fderiv hv1 z, e1, e0]
  have hc : ∀ j : Fin 2, ∀ e : ℝ × (ℝ × ℝ), ContinuousOn
      (fun p : ℝ × (ℝ × ℝ) => fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 j) Sx p e) Sx := by
    intro j e
    have h2 : ContinuousOn (fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 j) Sx) Sx :=
      (hG j).continuousOn_fderivWithin uniqueDiff_Sx (by simp)
    exact (ContinuousLinearMap.apply ℝ ℝ e).continuous.comp_continuousOn h2
  refine ContinuousOn.congr ((hc 1 (0, (1, 0))).sub (hc 0 (0, (0, 1)))) ?_
  intro p hp
  exact hEc p.1 hp.1 p.2

end UnforcedLeray.Short.IIIa.Exist
