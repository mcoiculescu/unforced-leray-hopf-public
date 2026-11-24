import UnforcedLeray.Short.PartIIa.Sub.F02

/-!
# Part II-a, task `PartII-a:F02/6`: second-order dilation bound

Source of record: `the November 2 reference manuscript`, lines 1363-1370
(dilation in `S(t)`).

This file proves the Prop `DilationTaylor2` of `Sub/F02.lean`: for `w` smooth, supported in
`‖y‖ ≤ R`, with `‖∇²w‖ ≤ M` and `b ∈ [1/2, 1]`,
`‖w(b·) - w - (b-1) y·∇w‖_p ≤ C M (1-b)²`, with `C` depending only on `R` and `p`.

Proof. Pointwise: the mean value inequality for `w` with the linear part `∇w(y)` frozen at `y`,
on the closed ball of radius `‖b•y - y‖` about `y`, uses that `∇w` is `M`-Lipschitz; this gives
`‖w(b•y) - w y - ∇w(y)(b•y - y)‖ ≤ M ‖b•y - y‖²` and `‖b•y - y‖ = (1-b)‖y‖`. Support: both
`w(b•y)` and `w y` and `∇w y` vanish when `‖y‖ > 2 max(R,0)`. The ball argument of
`DilationTaylor1` (copied here as `dilationTaylor2_ball_bound`) then gives the `L^p` bound with
`C = 4 max(R,0)² · vol(B_{2 max(R,0)})^{1/p}` (the constant is `4 R'²` rather than `2 R'²`
because the pointwise bound is used with constant `1`, not `1/2`).
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- The derivative of a field vanishes at every point outside the support radius. -/
theorem dilationTaylor2_fderiv_zero (w : SpatialField) (R : ℝ)
    (hsupp : ∀ y : Space, R < ‖y‖ → w y = 0) (z : Space) (hz : R < ‖z‖) :
    fderiv ℝ w z = 0 := by
  have hopen : IsOpen {u : Space | R < ‖u‖} := isOpen_lt continuous_const continuous_norm
  have hev : w =ᶠ[𝓝 z] (fun _ => (0 : Space)) := by
    filter_upwards [hopen.mem_nhds hz] with u hu
    exact hsupp u hu
  rw [hev.fderiv_eq]
  exact fderiv_const_apply _

/-- Pointwise second-order dilation bound: for `‖∇²w‖ ≤ M` and `b ≤ 1`,
`‖w(b•y) - w y - (b-1)•∇w(y)y‖ ≤ M (1-b)² ‖y‖²`. -/
theorem dilationTaylor2_pointwise (M b : ℝ) (w : SpatialField) (hw : ContDiff ℝ ∞ w)
    (hM : ∀ y : Space, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ M) (hM0 : 0 ≤ M) (hb2 : b ≤ 1) (y : Space) :
    ‖w (b • y) - w y - (b - 1) • fderiv ℝ w y y‖ ≤ M * (1 - b) ^ 2 * ‖y‖ ^ 2 := by
  have hdiff : ∀ x : Space, DifferentiableAt ℝ w x := fun x => (hw.differentiable (by simp)) x
  have hdiff1 : ∀ x : Space, DifferentiableAt ℝ (fderiv ℝ w) x := fun x =>
    ((ContDiff.fderiv_right (m := ∞) hw (by simp)).differentiable (by simp)) x
  -- the derivative of `w` is `M`-Lipschitz (mean value inequality on all of `Space`)
  have hlip : ∀ z : Space, ‖fderiv ℝ w z - fderiv ℝ w y‖ ≤ M * ‖z - y‖ := fun z =>
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiff1 x)
      (fun x _ => hM x) convex_univ (Set.mem_univ y) (Set.mem_univ z)
  have hr0 : 0 ≤ ‖b • y - y‖ := norm_nonneg _
  -- on the closed ball of radius `‖b•y - y‖` about `y`, the derivative differs from `∇w(y)`
  -- by at most `M` times that radius
  have hs : ∀ z ∈ Metric.closedBall y ‖b • y - y‖,
      ‖fderiv ℝ w z - fderiv ℝ w y‖ ≤ M * ‖b • y - y‖ := by
    intro z hz
    have hzy : ‖z - y‖ ≤ ‖b • y - y‖ := by
      have h := Metric.mem_closedBall.mp hz
      rwa [dist_eq_norm] at h
    exact (hlip z).trans (mul_le_mul_of_nonneg_left hzy hM0)
  have hbmem : b • y ∈ Metric.closedBall y ‖b • y - y‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le' (f := w) (φ := fderiv ℝ w y)
    (s := Metric.closedBall y ‖b • y - y‖) (C := M * ‖b • y - y‖)
    (fun x _ => hdiff x) hs (convex_closedBall y _) (Metric.mem_closedBall_self hr0) hbmem
  have hlin : fderiv ℝ w y (b • y - y) = (b - 1) • fderiv ℝ w y y := by
    rw [show b • y - y = (b - 1) • y by rw [sub_smul, one_smul], map_smul]
  have hnorm : ‖b • y - y‖ = (1 - b) * ‖y‖ := by
    rw [show b • y - y = (b - 1) • y by rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (show b - 1 ≤ 0 by linarith)]
    ring
  rw [hlin, hnorm] at hmv
  calc ‖w (b • y) - w y - (b - 1) • fderiv ℝ w y y‖
      ≤ M * ((1 - b) * ‖y‖) * ((1 - b) * ‖y‖) := hmv
    _ = M * (1 - b) ^ 2 * ‖y‖ ^ 2 := by ring

/-- An `L^r` bound for a `Space`-valued function vanishing off a closed ball
(copy of `dilationTaylor1_ball_bound`, kept in this file so that it does not import its sibling;
the statement is the same as `PhaseSpace.eLpNorm_le_of_ball`). -/
theorem dilationTaylor2_ball_bound (g : Space → Space) (R eta : ℝ)
    (hsupp : ∀ y, R < ‖y‖ → g y = 0) (hb : ∀ y, ‖y‖ ≤ R → ‖g y‖ ≤ eta) (r : ℝ≥0∞) :
    eLpNorm g r volume ≤
      volume (Metric.closedBall (0 : Space) R) ^ r.toReal⁻¹ * ENNReal.ofReal eta := by
  have hind : (Metric.closedBall (0 : Space) R).indicator g = g := by
    funext y
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · simp [hy]
    · have : R < ‖y‖ := by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
      simp [hy, hsupp y this]
  rw [← hind, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
  have h := eLpNorm_le_of_ae_bound (μ := volume.restrict (Metric.closedBall (0 : Space) R))
    (p := r) (f := g) (C := eta)
    (ae_restrict_of_forall_mem measurableSet_closedBall fun y hy =>
      hb y (by simpa [Metric.mem_closedBall, dist_zero_right] using hy))
  simpa [Measure.restrict_apply_univ] using h

/-- **Second-order dilation bound** (task `PartII-a:F02/6`): proves `DilationTaylor2`. -/
theorem dilationTaylor2 : UnforcedLeray.Short.PartIIa.DilationTaylor2 := by
  intro R p _hp1 _hpt
  have hR1 : R ≤ max R 0 := le_max_left R 0
  have hR0 : (0 : ℝ) ≤ max R 0 := le_max_right R 0
  refine ⟨4 * (max R 0) ^ 2 * (volume (Metric.closedBall (0 : Space) (2 * max R 0)) ^
      p.toReal⁻¹).toReal, ?_, ?_⟩
  · exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
  · intro M w hw hsupp hM b hb1 hb2
    have hM0 : 0 ≤ M := by
      have h0 := hM 0
      have hn := norm_nonneg (fderiv ℝ (fderiv ℝ w) 0)
      linarith
    have hb0 : 0 ≤ b := by linarith
    have hT : volume (Metric.closedBall (0 : Space) (2 * max R 0)) ^ p.toReal⁻¹ ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
        measure_closedBall_lt_top.ne
    -- the second-order difference vanishes outside the ball of radius `2 max R 0`
    have hsupp2 : ∀ y : Space, 2 * max R 0 < ‖y‖ →
        w (b • y) - w y - (b - 1) • fderiv ℝ w y y = 0 := by
      intro y hy
      have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
      have hyR : R < ‖y‖ := by linarith
      have hhalf : (1 / 2 : ℝ) * ‖y‖ ≤ b * ‖y‖ := mul_le_mul_of_nonneg_right hb1 hy0
      have hbyR : R < ‖b • y‖ := by
        rw [norm_smul, Real.norm_of_nonneg hb0]
        linarith
      simp [hsupp y hyR, hsupp (b • y) hbyR, dilationTaylor2_fderiv_zero w R hsupp y hyR]
    -- pointwise bound inside the ball
    have hbound : ∀ y : Space, ‖y‖ ≤ 2 * max R 0 →
        ‖w (b • y) - w y - (b - 1) • fderiv ℝ w y y‖ ≤ M * (1 - b) ^ 2 * (2 * max R 0) ^ 2 := by
      intro y hy
      have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
      have hsq : ‖y‖ ^ 2 ≤ (2 * max R 0) ^ 2 := by nlinarith
      have hMb : 0 ≤ M * (1 - b) ^ 2 := mul_nonneg hM0 (sq_nonneg _)
      exact (dilationTaylor2_pointwise M b w hw hM hM0 hb2 y).trans
        (mul_le_mul_of_nonneg_left hsq hMb)
    have hL := dilationTaylor2_ball_bound (fun y => w (b • y) - w y - (b - 1) • fderiv ℝ w y y)
      (2 * max R 0) (M * (1 - b) ^ 2 * (2 * max R 0) ^ 2) hsupp2 hbound p
    calc eLpNorm (fun y => w (b • y) - w y - (b - 1) • fderiv ℝ w y y) p volume
        ≤ volume (Metric.closedBall (0 : Space) (2 * max R 0)) ^ p.toReal⁻¹ *
            ENNReal.ofReal (M * (1 - b) ^ 2 * (2 * max R 0) ^ 2) := hL
      _ = ENNReal.ofReal ((volume (Metric.closedBall (0 : Space) (2 * max R 0)) ^
            p.toReal⁻¹).toReal * (M * (1 - b) ^ 2 * (2 * max R 0) ^ 2)) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hT]
      _ = ENNReal.ofReal (4 * (max R 0) ^ 2 * (volume (Metric.closedBall (0 : Space) (2 * max R 0)) ^
            p.toReal⁻¹).toReal * M * (1 - b) ^ 2) := by
          congr 1
          ring

end UnforcedLeray.Short.PartIIa
