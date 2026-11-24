import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_1
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Order.CompletePartialOrder

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- Second-derivative test, maximum form: a continuous function with a local maximum has
`f'' ≤ 0` at that point (in the sense of `deriv (deriv f)`). -/
theorem mp_deriv_deriv_le_zero (f : ℝ → ℝ) (x0 : ℝ) (hc : ContinuousAt f x0)
    (hmax : IsLocalMax f x0) : deriv (deriv f) x0 ≤ 0 := by
  by_contra h
  push_neg at h
  have hd : deriv f x0 = 0 := hmax.deriv_eq_zero
  have hmin : IsLocalMin f x0 := isLocalMin_of_deriv_deriv_pos h hd hc
  have hev : f =ᶠ[𝓝 x0] fun _ => f x0 := by
    filter_upwards [hmax, hmin] with y h1 h2
    exact le_antisymm h1 h2
  have hd2 : deriv f =ᶠ[𝓝 x0] deriv (fun _ => f x0) := hev.deriv
  have h3 : deriv (deriv f) x0 = deriv (deriv (fun _ => f x0)) x0 := by
    apply Filter.EventuallyEq.deriv_eq
    exact hd2
  simp at h3
  linarith

/-- Partial derivative in `η` of a plane function along a horizontal line. -/
theorem mp_hasDerivAt_pd1 (G : B0579.Plane → ℝ) (hG : Differentiable ℝ G) (a y : ℝ) :
    HasDerivAt (fun y : ℝ => G (a, y)) (B0579.pd 1 G (a, y)) y := by
  have hγ : HasDerivAt (fun y : ℝ => ((a, y) : B0579.Plane)) ((0 : ℝ), (1 : ℝ)) y :=
    (hasDerivAt_const y a).prodMk (hasDerivAt_id y)
  have h := (hG (a, y)).hasFDerivAt.comp_hasDerivAt y hγ
  have e : B0579.pd 1 G (a, y) = fderiv ℝ G (a, y) ((0 : ℝ), (1 : ℝ)) := by
    unfold B0579.pd
    simp [B0579.dir]
  rw [e]
  exact h

/-- Second-order partial in `η`, maximum form. -/
theorem mp_pd1_pd1_le_zero (G : B0579.Plane → ℝ) (hG : ContDiff ℝ 2 G) (a b : ℝ)
    (hmax : IsLocalMax (fun y : ℝ => G (a, y)) b) :
    B0579.pd 1 (B0579.pd 1 G) (a, b) ≤ 0 := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hfd : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hH : Differentiable ℝ (B0579.pd 1 G) := by
    have e : B0579.pd 1 G = fun z => fderiv ℝ G z ((0 : ℝ), (1 : ℝ)) := by
      funext z
      unfold B0579.pd
      simp [B0579.dir]
    rw [e]
    exact hfd.clm_apply (differentiable_const _)
  have hd : deriv (fun y : ℝ => G (a, y)) = fun y => B0579.pd 1 G (a, y) :=
    funext fun y => (mp_hasDerivAt_pd1 G hGd a y).deriv
  have hcont : ContinuousAt (fun y : ℝ => G (a, y)) b :=
    (hGd.continuous.comp (continuous_const.prodMk continuous_id)).continuousAt
  have h1 := mp_deriv_deriv_le_zero (fun y : ℝ => G (a, y)) b hcont hmax
  rw [hd] at h1
  have h2 : deriv (fun y : ℝ => B0579.pd 1 G (a, y)) b = B0579.pd 1 (B0579.pd 1 G) (a, b) :=
    (mp_hasDerivAt_pd1 (B0579.pd 1 G) hH a b).deriv
  rw [h2] at h1
  exact h1

end UnforcedLeray.Short.IIb
