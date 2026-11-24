import UnforcedLeray.Short.PartIIb.Sub.B1
import UnforcedLeray.Lib.LerayLp.Cutoff
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct

/-!
# Part II-b, task `PartII-b:B1`: the cutoff cross term is small (`CutoffCrossBound`)

Target: `UnforcedLeray.Short.IIb.CutoffCrossBound` (`Sub/B1.lean`, the definition with the
`3/q₀' = 21/11 < 2` remark). Source of record:
`the November 2 reference manuscript`, the cut-off of the Newton curl potential
(the cross term `∇χ_R × B` of `CurlCutoffProductRule`).

## Proof

Write `χ_R = cutoff R` and `C₀ = derivativeConstant 1`.

* every coordinate derivative satisfies `|∂ᵢ χ_R| ≤ C₀ / R` (from `cutoff_fderiv_le`), hence
  `‖∇χ_R‖ ≤ 3 C₀ / R` everywhere;
* `∇χ_R = 0` off the annulus `R ≤ ‖y‖ ≤ 2R` (`spatialTestDerivative_cutoff_of_lt/_of_gt`);
* `‖B y‖ ≤ M / (1 + ‖y‖) ≤ M / R` on the annulus, and `M ≥ 0`;
* `‖a × b‖ ≤ ‖a‖ ‖b‖` (`InnerProductGeometry.norm_ofLp_crossProduct`).

So the integrand is pointwise at most `3 C₀ M R⁻²` on `closedBall 0 (2R)` and zero outside it.
Its `L^{r}` norm with `r = conjExp q₀ = 11/7` is at most `3 C₀ M R⁻² ((2R)³ V)^{7/11}`, where
`V = vol(ball 0 1)` (as a real number). Since `R⁻² R^{21/11} = R^{-1/11}`, the choice
`C = 3 C₀ (8V)^{7/11}` works.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.RieszLp

/-- The cross product on `ℝ³` is bounded by the product of the norms. -/
theorem cutoffCrossBound_norm_crossProd_le (a b : Space) :
    ‖Blueprint.crossProd a b‖ ≤ ‖a‖ * ‖b‖ := by
  unfold Blueprint.crossProd
  rw [InnerProductGeometry.norm_ofLp_crossProduct]
  exact mul_le_of_le_one_right (by positivity) (Real.sin_le_one _)

/-- Each coordinate derivative of the cut-off is bounded by `C₀ / R`, with `C₀ = derivativeConstant 1`. -/
theorem cutoffCrossBound_abs_partial_le {R : ℝ} (hR : 0 < R) (y : Space) (i : Fin 3) :
    |spatialTestDerivative i (NavierStokesR3.ComparisonCutoffs.cutoff R) y| ≤
      NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 / R := by
  have e1 := NavierStokesR3.ComparisonCutoffs.cutoff_fderiv_le hR y
  have e2 := (fderiv ℝ (NavierStokesR3.ComparisonCutoffs.cutoff R) y).le_opNorm
    (coordinateVector i)
  rw [RieszLp.norm_coordinateVector, mul_one] at e2
  rw [← Real.norm_eq_abs]
  exact e2.trans e1

/-- The gradient of the cut-off is bounded by `3 C₀ / R` everywhere. -/
theorem cutoffCrossBound_norm_gradField_le {R : ℝ} (hR : 0 < R) (y : Space) :
    ‖gradField (NavierStokesR3.ComparisonCutoffs.cutoff R) y‖ ≤
      3 * (NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 / R) := by
  have h1 := norm_sum_smul_coordinateVector_le
    (fun i => spatialTestDerivative i (NavierStokesR3.ComparisonCutoffs.cutoff R) y)
  have h2 : ∑ i : Fin 3, |spatialTestDerivative i (NavierStokesR3.ComparisonCutoffs.cutoff R) y| ≤
      ∑ _i : Fin 3, NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 / R :=
    Finset.sum_le_sum fun i _ => cutoffCrossBound_abs_partial_le hR y i
  have h3 : ∑ _i : Fin 3, NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 / R =
      3 * (NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 / R) := by
    simp [Finset.sum_const]
  exact h1.trans (h2.trans h3.le)

/-- Outside the annulus `R ≤ ‖y‖ ≤ 2R` the gradient of the cut-off vanishes. -/
theorem cutoffCrossBound_gradField_eq_zero {R : ℝ} (hR : 0 < R) {y : Space}
    (hy : ‖y‖ < R ∨ 2 * R < ‖y‖) :
    gradField (NavierStokesR3.ComparisonCutoffs.cutoff R) y = 0 := by
  unfold gradField
  refine Finset.sum_eq_zero fun i _ => ?_
  have h0 : spatialTestDerivative i (NavierStokesR3.ComparisonCutoffs.cutoff R) y = 0 := by
    rcases hy with h | h
    · exact spatialTestDerivative_cutoff_of_lt hR h i
    · exact spatialTestDerivative_cutoff_of_gt hR h i
  rw [h0, zero_smul]

/-- The exponent `conjExp q₀ = 11/7` (the dual of `q₀ = 11/4`). -/
theorem cutoffCrossBound_conjExp_eq :
    conjExp q0E = ENNReal.ofReal (11 / 7) := by
  have hq0 : q0E = ENNReal.ofReal (11 / 4) := rfl
  have h1 : (ENNReal.ofReal (11 / 4))⁻¹ = ENNReal.ofReal (4 / 11) := by
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 11 / 4)]
    norm_num
  have h2 : (1 : ℝ≥0∞) - ENNReal.ofReal (4 / 11) = ENNReal.ofReal (7 / 11) := by
    have := ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 4 / 11)
    rw [ENNReal.ofReal_one] at this
    rw [← this]
    norm_num
  have h3 : (ENNReal.ofReal (7 / 11))⁻¹ = ENNReal.ofReal (11 / 7) := by
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 7 / 11)]
    norm_num
  unfold conjExp
  rw [hq0, h1, h2, h3]

/-- **Cut-off cross term.** The `L^{q₀'}` norm of `∇χ_R × B` is `≲ M R^{-1/11}`, for `R ≥ 1`. -/
theorem cutoffCrossBound : UnforcedLeray.Short.IIb.CutoffCrossBound := by
  unfold CutoffCrossBound
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = (volume (Metric.ball (0 : Space) 1)).toReal := ⟨_, rfl⟩
  have hKtop : volume (Metric.ball (0 : Space) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hVnn : 0 ≤ V := by
    rw [hVdef]
    exact ENNReal.toReal_nonneg
  have hVfin : volume (Metric.ball (0 : Space) 1) = ENNReal.ofReal V := by
    rw [hVdef, ENNReal.ofReal_toReal hKtop]
  have hC₀ : 0 < NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 :=
    NavierStokesR3.ComparisonCutoffs.derivativeConstant_pos 1
  refine ⟨3 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 * (8 * V) ^ (7 / 11 : ℝ), ?_⟩
  intro M B hB R hR1
  have hR0 : 0 < R := by linarith
  have hM : 0 ≤ M := by
    have h0 := hB 0
    rw [norm_zero, add_zero, div_one] at h0
    exact (norm_nonneg _).trans h0
  have hnn : 0 ≤ 3 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 * M / R ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀.le) hM) (sq_nonneg R)
  have hind0 : ∀ z : Space,
      0 ≤ (Metric.closedBall (0 : Space) (2 * R)).indicator
        (fun _ => 3 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 * M / R ^ 2) z := by
    intro z
    classical
    rw [Set.indicator_apply]
    split_ifs
    · exact hnn
    · exact le_rfl
  -- pointwise bound
  have hpt : ∀ y : Space,
      ‖Blueprint.crossProd (gradField (NavierStokesR3.ComparisonCutoffs.cutoff R) y) (B y)‖ ≤
        (Metric.closedBall (0 : Space) (2 * R)).indicator
          (fun _ => 3 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 * M / R ^ 2) y := by
    intro y
    by_cases hin : ‖y‖ < R ∨ 2 * R < ‖y‖
    · have hz := cutoffCrossBound_gradField_eq_zero hR0 hin
      have hk := cutoffCrossBound_norm_crossProd_le
        (gradField (NavierStokesR3.ComparisonCutoffs.cutoff R) y) (B y)
      rw [hz, norm_zero, zero_mul] at hk
      rw [hz]
      exact hk.trans (hind0 y)
    · rw [not_or, not_lt, not_lt] at hin
      obtain ⟨h1, h2⟩ := hin
      have hmem : y ∈ Metric.closedBall (0 : Space) (2 * R) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact h2
      rw [Set.indicator_of_mem hmem]
      have hgrad := cutoffCrossBound_norm_gradField_le hR0 y
      have hBy : ‖B y‖ ≤ M / R :=
        (hB y).trans (div_le_div_of_nonneg_left hM hR0 (by linarith))
      have hk := cutoffCrossBound_norm_crossProd_le
        (gradField (NavierStokesR3.ComparisonCutoffs.cutoff R) y) (B y)
      calc ‖Blueprint.crossProd (gradField (NavierStokesR3.ComparisonCutoffs.cutoff R) y) (B y)‖
          ≤ ‖gradField (NavierStokesR3.ComparisonCutoffs.cutoff R) y‖ * ‖B y‖ := hk
        _ ≤ (3 * (NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 / R)) * (M / R) :=
            mul_le_mul hgrad hBy (norm_nonneg _)
              (mul_nonneg (by norm_num) (div_nonneg hC₀.le hR0.le))
        _ = 3 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 * M / R ^ 2 := by ring
  -- the L^r norm of the indicator
  have hr_eq := cutoffCrossBound_conjExp_eq
  have hrne0 : conjExp q0E ≠ 0 := by
    rw [hr_eq]
    exact (ENNReal.ofReal_pos.2 (by norm_num : (0 : ℝ) < 11 / 7)).ne'
  have hrtop : conjExp q0E ≠ ⊤ := by
    rw [hr_eq]
    exact ENNReal.ofReal_ne_top
  have hr : (conjExp q0E).toReal = 11 / 7 := by
    rw [hr_eq, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 11 / 7)]
  have hexp : 1 / (conjExp q0E).toReal = 7 / 11 := by
    rw [hr]
    norm_num
  have hS : MeasurableSet (Metric.closedBall (0 : Space) (2 * R)) := measurableSet_closedBall
  have hfin3 : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have hvol : volume (Metric.closedBall (0 : Space) (2 * R)) =
      ENNReal.ofReal ((2 * R) ^ 3 * V) := by
    rw [Measure.addHaar_closedBall volume (0 : Space) (by linarith : (0 : ℝ) ≤ 2 * R), hfin3,
      hVfin, ENNReal.ofReal_mul (pow_nonneg (by linarith : (0 : ℝ) ≤ 2 * R) 3)]
  have hEL : eLpNorm ((Metric.closedBall (0 : Space) (2 * R)).indicator
      (fun _ => 3 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 * M / R ^ 2))
      (conjExp q0E) volume =
      ENNReal.ofReal (3 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 * M / R ^ 2) *
        ENNReal.ofReal ((2 * R) ^ 3 * V) ^ (1 / (conjExp q0E).toReal) := by
    rw [eLpNorm_indicator_const hS hrne0 hrtop, Real.enorm_eq_ofReal hnn, hvol]
  have hX : 0 ≤ (2 * R) ^ 3 * V := mul_nonneg (pow_nonneg (by linarith) 3) hVnn
  have hXpow : ((2 * R) ^ 3 * V) ^ (7 / 11 : ℝ) =
      R ^ (21 / 11 : ℝ) * (8 * V) ^ (7 / 11 : ℝ) := by
    have e1 : (2 * R) ^ 3 * V = R ^ (3 : ℝ) * (8 * V) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [e1, Real.mul_rpow (Real.rpow_nonneg hR0.le 3) (mul_nonneg (by norm_num) hVnn),
      ← Real.rpow_mul hR0.le]
    norm_num
  have hRexp : R ^ (-(1 / 11 : ℝ)) = (R ^ 2)⁻¹ * R ^ (21 / 11 : ℝ) := by
    rw [show -(1 / 11 : ℝ) = -2 + 21 / 11 by norm_num, Real.rpow_add hR0,
      Real.rpow_neg hR0.le, Real.rpow_two]
  calc _ ≤ eLpNorm ((Metric.closedBall (0 : Space) (2 * R)).indicator
        (fun _ => 3 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 * M / R ^ 2))
        (conjExp q0E) volume := eLpNorm_mono_real hpt
    _ = ENNReal.ofReal (3 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 * M / R ^ 2 *
          ((2 * R) ^ 3 * V) ^ (7 / 11 : ℝ)) := by
        rw [hEL, hexp, ENNReal.ofReal_rpow_of_nonneg hX (by norm_num : (0 : ℝ) ≤ 7 / 11),
          ENNReal.ofReal_mul hnn]
    _ ≤ ENNReal.ofReal (3 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 *
          (8 * V) ^ (7 / 11 : ℝ) * M * R ^ (-(1 / 11 : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        apply le_of_eq
        rw [hXpow, hRexp]
        ring

end UnforcedLeray.Short.IIb
