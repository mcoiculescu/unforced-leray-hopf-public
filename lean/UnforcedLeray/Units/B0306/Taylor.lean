import UnforcedLeray.Statement
import Mathlib.Analysis.Calculus.MeanValue

/-!
# B0306 helper: first-order Taylor expansion with quadratic remainder

Helper module of blueprint unit B0306 (`background:eq:2.48`, `paper/main.tex` lines
5909--5921, infrastructure INF29): "Taylor expand through first order ... The quadratic remainder
has the displayed order" (tex lines 5916--5918). For a smooth `f` and `g = D^j f`, two
applications of the mean value inequality on balls give
`|g(y - x) - g(y) - Dg(y)(-x)| ≤ M |x|²` whenever `|D^{j+2} f| ≤ M` on `B̄(y, r)` and `|x| ≤ r`.
-/

set_option autoImplicit false

noncomputable section

open Metric
open scoped ContDiff

namespace UnforcedLeray.B0306

/-- Quadratic Taylor remainder of `D^j f` about `y`, controlled by `D^{j+2} f` on a ball. -/
theorem taylor_two {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : Space → G}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) {y : Space} {r M : ℝ}
    (hM : ∀ z ∈ closedBall y r, ‖iteratedFDeriv ℝ (j + 2) f z‖ ≤ M) {x : Space}
    (hx : ‖x‖ ≤ r) :
    ‖iteratedFDeriv ℝ j f (y - x) - iteratedFDeriv ℝ j f y -
        fderiv ℝ (iteratedFDeriv ℝ j f) y (-x)‖ ≤ M * ‖x‖ ^ 2 := by
  have hr : 0 ≤ r := (norm_nonneg x).trans hx
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y (mem_closedBall_self hr))
  have hd0 : Differentiable ℝ (iteratedFDeriv ℝ j f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
  have hd1 : Differentiable ℝ (iteratedFDeriv ℝ (j + 1) f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
  have hfd : fderiv ℝ (iteratedFDeriv ℝ j f) =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Space) G ∘
        iteratedFDeriv ℝ (j + 1) f := fderiv_iteratedFDeriv
  have hstep : ∀ z ∈ closedBall y r, ‖fderiv ℝ (iteratedFDeriv ℝ j f) z -
      fderiv ℝ (iteratedFDeriv ℝ j f) y‖ ≤ M * ‖z - y‖ := by
    intro z hz
    rw [hfd, Function.comp_apply, Function.comp_apply, ← LinearIsometryEquiv.map_sub,
      LinearIsometryEquiv.norm_map]
    refine (convex_closedBall y r).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hd1 w) (fun w hw => ?_) (mem_closedBall_self hr) hz
    rw [norm_fderiv_iteratedFDeriv]
    exact hM w hw
  have hbound : ∀ w ∈ closedBall y ‖x‖, ‖fderiv ℝ (iteratedFDeriv ℝ j f) w -
      fderiv ℝ (iteratedFDeriv ℝ j f) y‖ ≤ M * ‖x‖ := by
    intro w hw
    refine (hstep w (closedBall_subset_closedBall hx hw)).trans ?_
    rw [← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (mem_closedBall.1 hw) hM0
  have hyx : y - x ∈ closedBall y ‖x‖ := by
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
  have key := (convex_closedBall y ‖x‖).norm_image_sub_le_of_norm_fderiv_le'
    (fun w _ => hd0 w) hbound (mem_closedBall_self (norm_nonneg x)) hyx
  rw [sub_sub_cancel_left, norm_neg] at key
  calc _ ≤ M * ‖x‖ * ‖x‖ := key
    _ = M * ‖x‖ ^ 2 := by ring

end UnforcedLeray.B0306
