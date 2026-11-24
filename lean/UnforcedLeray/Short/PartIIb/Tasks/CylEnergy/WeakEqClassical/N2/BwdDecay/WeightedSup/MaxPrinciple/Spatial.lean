import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_1_3
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.MaxPrinciple.Lap

/-!
# `MpSpatial` (SP 2100-2105): first and second derivative test at a global maximum on the plane.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.IIb

theorem mp_hasDerivAt_pd0 (G : B0579.Plane → ℝ) (hG : Differentiable ℝ G) (a b : ℝ) :
    HasDerivAt (fun q : ℝ => G (q, b)) (B0579.pd 0 G (a, b)) a := by
  have hγ : HasDerivAt (fun q : ℝ => ((q, b) : B0579.Plane)) ((1 : ℝ), (0 : ℝ)) a :=
    (hasDerivAt_id a).prodMk (hasDerivAt_const a b)
  have h := (hG (a, b)).hasFDerivAt.comp_hasDerivAt a hγ
  have e : B0579.pd 0 G (a, b) = fderiv ℝ G (a, b) ((1 : ℝ), (0 : ℝ)) := by
    unfold B0579.pd
    simp [B0579.dir]
  rw [e]
  exact h

theorem mp_pd0_pd0_le_zero (G : B0579.Plane → ℝ) (hG : ContDiff ℝ 2 G) (a b : ℝ)
    (hmax : IsLocalMax (fun q : ℝ => G (q, b)) a) :
    B0579.pd 0 (B0579.pd 0 G) (a, b) ≤ 0 := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hH := mp_pd_diff hG 0
  have hd : deriv (fun q : ℝ => G (q, b)) = fun q => B0579.pd 0 G (q, b) :=
    funext fun q => (mp_hasDerivAt_pd0 G hGd q b).deriv
  have hcont : ContinuousAt (fun q : ℝ => G (q, b)) a :=
    (hGd.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt
  have h1 := mp_deriv_deriv_le_zero (fun q : ℝ => G (q, b)) a hcont hmax
  rw [hd] at h1
  have h2 : deriv (fun q : ℝ => B0579.pd 0 G (q, b)) a = B0579.pd 0 (B0579.pd 0 G) (a, b) :=
    (mp_hasDerivAt_pd0 (B0579.pd 0 G) hH a b).deriv
  rw [h2] at h1
  exact h1

theorem mpSpatial : MpSpatial := by
  intro G x0 hG hmax
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  obtain ⟨a, b⟩ := x0
  have l0 : IsLocalMax (fun q : ℝ => G (q, b)) a :=
    Filter.Eventually.of_forall (fun q => hmax (q, b))
  have l1 : IsLocalMax (fun y : ℝ => G (a, y)) b :=
    Filter.Eventually.of_forall (fun y => hmax (a, y))
  have d0 := l0.deriv_eq_zero
  have d1 := l1.deriv_eq_zero
  rw [(mp_hasDerivAt_pd0 G hGd a b).deriv] at d0
  rw [(mp_hasDerivAt_pd1 G hGd a b).deriv] at d1
  refine ⟨d0, d1, ?_⟩
  unfold lapP
  have s0 := mp_pd0_pd0_le_zero G hG a b l0
  have s1 := mp_pd1_pd1_le_zero G hG a b l1
  linarith

end UnforcedLeray.Short.IIb
