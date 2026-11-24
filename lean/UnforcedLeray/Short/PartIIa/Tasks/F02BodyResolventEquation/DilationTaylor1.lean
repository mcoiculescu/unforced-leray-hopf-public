import UnforcedLeray.Short.PartIIa.Sub.F02

/-!
# Part II-a, task `PartII-a:F02/5`: first-order dilation bound

Source of record: `the November 2 reference manuscript`, lines 1363-1370
(dilation in `S(t)`).

This file proves the Prop `DilationTaylor1` of `Sub/F02.lean`: for `w` smooth, supported in
`‖y‖ ≤ R`, with `‖∇w‖ ≤ M` and `b ∈ [1/2, 1]`,
`‖w(b·) - w‖_p ≤ C M (1 - b)`, with `C` depending only on `R` and `p`.

Proof: the mean value inequality on the segment from `b • y` to `y` gives
`‖w(b•y) - w y‖ ≤ M (1-b) ‖y‖`. Both terms vanish when `‖y‖ > 2 max(R,0)`, so the difference
lives in the ball of radius `2 max(R,0)` and is bounded there by `M (1-b) 2 max(R,0)`.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Pointwise dilation bound from the mean value inequality on the segment from `b • y` to `y`. -/
theorem dilationTaylor1_pointwise (M b : ℝ) (w : SpatialField) (hw : ContDiff ℝ ∞ w)
    (hM : ∀ y : Space, ‖fderiv ℝ w y‖ ≤ M) (hb2 : b ≤ 1) (y : Space) :
    ‖w (b • y) - w y‖ ≤ M * (1 - b) * ‖y‖ := by
  have hdiff : ∀ x : Space, DifferentiableAt ℝ w x := fun x => (hw.differentiable (by simp)) x
  have hmvt : ‖w y - w (b • y)‖ ≤ M * ‖y - b • y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hdiff x : ∀ x ∈ (Set.univ : Set Space), DifferentiableAt ℝ w x)
      (fun x _ => hM x : ∀ x ∈ (Set.univ : Set Space), ‖fderiv ℝ w x‖ ≤ M)
      convex_univ (Set.mem_univ (b • y)) (Set.mem_univ y)
  have h1b : 0 ≤ 1 - b := by linarith
  have hsub : y - b • y = (1 - b) • y := by rw [sub_smul, one_smul]
  have hnorm : ‖y - b • y‖ = (1 - b) * ‖y‖ := by
    rw [hsub, norm_smul, Real.norm_of_nonneg h1b]
  calc ‖w (b • y) - w y‖ = ‖w y - w (b • y)‖ := norm_sub_rev _ _
    _ ≤ M * ‖y - b • y‖ := hmvt
    _ = M * (1 - b) * ‖y‖ := by rw [hnorm]; ring

/-- An `L^r` bound for a `Space`-valued function vanishing off a closed ball
(copy of `PhaseSpace.eLpNorm_le_of_ball`, which is stated for `CVec3`-valued functions). -/
theorem dilationTaylor1_ball_bound (g : Space → Space) (R eta : ℝ)
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

/-- **First-order dilation bound** (task `PartII-a:F02/5`): proves `DilationTaylor1`. -/
theorem dilationTaylor1 : UnforcedLeray.Short.PartIIa.DilationTaylor1 := by
  intro R p hp1 hpt
  have hR1 : R ≤ max R 0 := le_max_left R 0
  have hR0 : (0 : ℝ) ≤ max R 0 := le_max_right R 0
  refine ⟨2 * max R 0 * (volume (Metric.closedBall (0 : Space) (2 * max R 0)) ^
      p.toReal⁻¹).toReal, ?_, ?_⟩
  · exact mul_nonneg (by linarith) ENNReal.toReal_nonneg
  · intro M w hw hsupp hM b hb1 hb2
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hb0 : 0 ≤ b := by linarith
    have hT : volume (Metric.closedBall (0 : Space) (2 * max R 0)) ^ p.toReal⁻¹ ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
        measure_closedBall_lt_top.ne
    -- the difference vanishes outside the ball of radius `2 max R 0`
    have hsupp2 : ∀ y : Space, 2 * max R 0 < ‖y‖ → w (b • y) - w y = 0 := by
      intro y hy
      have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
      have hyR : R < ‖y‖ := by linarith
      have hhalf : (1 / 2 : ℝ) * ‖y‖ ≤ b * ‖y‖ := mul_le_mul_of_nonneg_right hb1 hy0
      have hbyR : R < ‖b • y‖ := by
        rw [norm_smul, Real.norm_of_nonneg hb0]
        linarith
      simp [hsupp y hyR, hsupp (b • y) hbyR]
    -- pointwise bound inside the ball
    have hbound : ∀ y : Space, ‖y‖ ≤ 2 * max R 0 →
        ‖w (b • y) - w y‖ ≤ M * (1 - b) * (2 * max R 0) := by
      intro y hy
      have hMb : 0 ≤ M * (1 - b) := mul_nonneg hM0 (by linarith)
      calc ‖w (b • y) - w y‖ ≤ M * (1 - b) * ‖y‖ :=
            dilationTaylor1_pointwise M b w hw hM hb2 y
        _ ≤ M * (1 - b) * (2 * max R 0) := mul_le_mul_of_nonneg_left hy hMb
    have hL := dilationTaylor1_ball_bound (fun y => w (b • y) - w y) (2 * max R 0)
      (M * (1 - b) * (2 * max R 0)) (fun y hy => hsupp2 y hy) (fun y hy => hbound y hy) p
    calc eLpNorm (fun y => w (b • y) - w y) p volume
        ≤ volume (Metric.closedBall (0 : Space) (2 * max R 0)) ^ p.toReal⁻¹ *
            ENNReal.ofReal (M * (1 - b) * (2 * max R 0)) := hL
      _ = ENNReal.ofReal ((volume (Metric.closedBall (0 : Space) (2 * max R 0)) ^
            p.toReal⁻¹).toReal * (M * (1 - b) * (2 * max R 0))) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hT]
      _ = ENNReal.ofReal (2 * max R 0 * (volume (Metric.closedBall (0 : Space) (2 * max R 0)) ^
            p.toReal⁻¹).toReal * M * (1 - b)) := by
          congr 1
          ring

end UnforcedLeray.Short.PartIIa
