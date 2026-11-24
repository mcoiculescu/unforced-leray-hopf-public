import UnforcedLeray.Short.PartIIIa.Sub.T15

/-!
# Part III-a, task `PartIII-a:T15/8`: second partials, calculus (SP 3598-3610)

Proves `part2Calculus : Part2Calculus` (`Sub/T15.lean`). Source of record:
`the November 2 reference manuscript`, lines 3598-3610 (the kernel
`K_t = δ_{ij}G_t + ∂_i∂_j ∫_t^∞ G_a da` and `K_0 = D²(4π|x|)^{-1}` off the origin).

Strategy.
* `part2_eq_hess`: where `fderiv h` is differentiable at `y`,
  `part2 h i k y = (D²h y e_i) e_k` with `D²h = fderiv (fderiv h)` (`fderiv_clm_apply`).
* `part2_eventually_eq`: near `x` the function `f` is `C²`, so `part2 f i k` agrees with
  `p2Phi i k ∘ D²f`, where `p2Phi i k A = (A e_i) e_k` has operator norm at most `1`.
* (a) and (b): `D²f` is `C^∞` at `x` (pointwise, `ContDiffAt.fderiv_right` twice). The germ
  equality transports `iteratedFDeriv`, and `norm_iteratedFDeriv_fderiv` twice gives `n + 2`.
* (c): `f` and `g` are `C²` on a neighbourhood of every point near `x`
  (`Filter.Eventually.eventually_nhds`), so `fderiv` is linear there (`fderiv_sub`).

Only pointwise `C^∞` is assumed at `x`, so the eventual smoothness is taken at the finite
order `2` (`ContDiffAt.eventually` requires `n ≠ ∞`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Evaluation at the coordinate vector `e_j` on `Space →L ℝ`. -/
private def p2Ev (j : Fin 3) : (Space →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.apply ℝ ℝ (coordinateVector j)

private lemma p2Ev_apply (j : Fin 3) (A : Space →L[ℝ] ℝ) :
    p2Ev j A = A (coordinateVector j) := rfl

private lemma norm_coordinateVector_eq_one (j : Fin 3) : ‖coordinateVector j‖ = 1 := by
  simp [coordinateVector]

private lemma norm_p2Ev_le (j : Fin 3) : ‖p2Ev j‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun A => ?_)
  have h1 : ‖A (coordinateVector j)‖ ≤ ‖A‖ * ‖coordinateVector j‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [norm_coordinateVector_eq_one, mul_one] at h1
  rw [p2Ev_apply, one_mul]
  exact h1

/-- The second partial as two evaluations: `part2 f i k = e_i ∘ fderiv (e_k ∘ fderiv f)`. -/
private lemma part2_eq_ev (f : Space → ℝ) (i k : Fin 3) :
    part2 f i k = fun y => p2Ev i (fderiv ℝ (fun z => p2Ev k (fderiv ℝ f z)) y) := rfl

/-- The second partial in Hessian form, at a point where `fderiv h` is differentiable. -/
private lemma part2_eq_hess (h : Space → ℝ) (i k : Fin 3) (y : Space)
    (hd : DifferentiableAt ℝ (fderiv ℝ h) y) :
    part2 h i k y = fderiv ℝ (fderiv ℝ h) y (coordinateVector i) (coordinateVector k) := by
  have hu : DifferentiableAt ℝ (fun _ : Space => coordinateVector k) y :=
    differentiableAt_const _
  have hc : fderiv ℝ (fun z => fderiv ℝ h z (coordinateVector k)) y =
      (fderiv ℝ (fderiv ℝ h) y).flip (coordinateVector k) := by
    have := fderiv_clm_apply (u := fun _ : Space => coordinateVector k) hd hu
    simpa [fderiv_const_apply] using this
  unfold part2
  rw [hc]
  simp

private lemma diff_fderiv_of_two {h : Space → ℝ} {y : Space} (hh : ContDiffAt ℝ 2 h y) :
    DifferentiableAt ℝ (fderiv ℝ h) y :=
  (hh.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt one_ne_zero

private lemma contDiffAt_fderiv_inf {h : Space → ℝ} {y : Space}
    (hh : ContDiffAt ℝ ∞ h y) : ContDiffAt ℝ ∞ (fderiv ℝ h) y :=
  ContDiffAt.fderiv_right (m := ∞) hh (by simp)

/-- **Second partials: calculus** (`PartIII-a:T15/8`). -/
theorem part2Calculus : UnforcedLeray.Short.IIIa.Part2Calculus := by
  intro f g x hf hg i k
  have hG : ContDiffAt ℝ ∞ (fun z => p2Ev k (fderiv ℝ f z)) x :=
    ContDiffAt.comp x (p2Ev k).contDiff.contDiffAt (contDiffAt_fderiv_inf hf)
  have hDG : ContDiffAt ℝ ∞ (fderiv ℝ (fun z => p2Ev k (fderiv ℝ f z))) x :=
    contDiffAt_fderiv_inf hG
  refine ⟨?_, ?_, ?_⟩
  · -- (a) smoothness of `part2 f i k` at `x`
    rw [part2_eq_ev f i k]
    exact ContDiffAt.comp x (p2Ev i).contDiff.contDiffAt hDG
  · -- (b) derivative bound: each evaluation has norm at most one
    intro n
    have hn : (n : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by simp
    have hn1 : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by simp
    have hfd1 : ‖iteratedFDeriv ℝ n (fderiv ℝ (fun z => p2Ev k (fderiv ℝ f z))) x‖ =
        ‖iteratedFDeriv ℝ (n + 1) (fun z => p2Ev k (fderiv ℝ f z)) x‖ :=
      norm_iteratedFDeriv_fderiv
    have hfd2 : ‖iteratedFDeriv ℝ (n + 1) (fderiv ℝ f) x‖ =
        ‖iteratedFDeriv ℝ (n + 2) f x‖ :=
      norm_iteratedFDeriv_fderiv
    have hc1 : ‖iteratedFDeriv ℝ n
        (fun y => p2Ev i (fderiv ℝ (fun z => p2Ev k (fderiv ℝ f z)) y)) x‖ ≤
        ‖p2Ev i‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ (fun z => p2Ev k (fderiv ℝ f z))) x‖ :=
      ContinuousLinearMap.norm_iteratedFDeriv_comp_left (n := n) (p2Ev i) hDG hn
    have hc2 : ‖iteratedFDeriv ℝ (n + 1) (fun z => p2Ev k (fderiv ℝ f z)) x‖ ≤
        ‖p2Ev k‖ * ‖iteratedFDeriv ℝ (n + 1) (fderiv ℝ f) x‖ :=
      ContinuousLinearMap.norm_iteratedFDeriv_comp_left (n := n + 1) (p2Ev k)
        (contDiffAt_fderiv_inf hf) hn1
    rw [part2_eq_ev f i k]
    calc ‖iteratedFDeriv ℝ n
          (fun y => p2Ev i (fderiv ℝ (fun z => p2Ev k (fderiv ℝ f z)) y)) x‖
        ≤ ‖p2Ev i‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ (fun z => p2Ev k (fderiv ℝ f z))) x‖ := hc1
      _ ≤ 1 * ‖iteratedFDeriv ℝ n (fderiv ℝ (fun z => p2Ev k (fderiv ℝ f z))) x‖ :=
          mul_le_mul_of_nonneg_right (norm_p2Ev_le i) (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ (n + 1) (fun z => p2Ev k (fderiv ℝ f z)) x‖ := by
          rw [one_mul, hfd1]
      _ ≤ ‖p2Ev k‖ * ‖iteratedFDeriv ℝ (n + 1) (fderiv ℝ f) x‖ := hc2
      _ ≤ 1 * ‖iteratedFDeriv ℝ (n + 1) (fderiv ℝ f) x‖ :=
          mul_le_mul_of_nonneg_right (norm_p2Ev_le k) (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ (n + 2) f x‖ := by
          rw [one_mul, hfd2]
  · -- (c) locality and linearity of `part2`
    have h2fx : ContDiffAt ℝ 2 f x := hf.of_le (by simp)
    have h2gx : ContDiffAt ℝ 2 g x := hg.of_le (by simp)
    have hall : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ 2 f z ∧ ContDiffAt ℝ 2 g z :=
      (h2fx.eventually (by norm_num)).and (h2gx.eventually (by norm_num))
    filter_upwards [hall.eventually_nhds] with y hy
    have hfy : ContDiffAt ℝ 2 f y := hy.self_of_nhds.1
    have hgy : ContDiffAt ℝ 2 g y := hy.self_of_nhds.2
    have hfgy : ContDiffAt ℝ 2 (fun z => f z - g z) y := hfy.sub hgy
    have hdiff : fderiv ℝ (fun w => f w - g w) =ᶠ[𝓝 y]
        fun z => fderiv ℝ f z - fderiv ℝ g z := by
      filter_upwards [hy] with z hz
      exact fderiv_sub (hz.1.differentiableAt (by norm_num)) (hz.2.differentiableAt (by norm_num))
    have hsub : fderiv ℝ (fun z => fderiv ℝ f z - fderiv ℝ g z) y =
        fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ g) y :=
      fderiv_sub (diff_fderiv_of_two hfy) (diff_fderiv_of_two hgy)
    show part2 (fun w => f w - g w) i k y = part2 f i k y - part2 g i k y
    simp only [part2_eq_hess (fun w => f w - g w) i k y (diff_fderiv_of_two hfgy),
      part2_eq_hess f i k y (diff_fderiv_of_two hfy),
      part2_eq_hess g i k y (diff_fderiv_of_two hgy), hdiff.fderiv_eq, hsub,
      ContinuousLinearMap.sub_apply]

end UnforcedLeray.Short.IIIa
