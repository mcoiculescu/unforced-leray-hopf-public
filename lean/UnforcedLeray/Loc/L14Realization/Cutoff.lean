import UnforcedLeray.TestFunctions
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Step L14, helpers: spatial cutoffs `χ_R(x) = χ(x/R)`

Support for `Loc/L14Realization.lean` (step L14 `RealizationStep`, `paper/main.tex`
lines 539–561, blueprint units B1030 and B1032). The integrations by parts behind the
trilinear cancellation (line 547, "multiplication by `u` gives the energy identity") and the
pressure identity (line 561, "this recovers the full pressure equation") pair quadratic
`L¹` quantities with smooth functions that are bounded but not compactly supported. They
are obtained from the compact-test identities by the cutoffs `χ_R(x) = χ(x/R)` of a fixed
bump `χ` (`χ = 1` on the unit ball, supported in the ball of radius `2`), `R = n + 1 → ∞`:
`χ_R → 1` and `∂ⱼχ_R → 0` pointwise with `0 ≤ χ_R ≤ 1` and `|∂ⱼχ_R| ≤ B` uniformly, so
dominated convergence applies against every `L¹` function.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L14

/-- The fixed bump `χ`: `1` on the closed unit ball, supported in the ball of radius `2`. -/
def baseBump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cutoff `χ_R(x) = χ(x / R)`. -/
def cutoff (R : ℝ) (x : Space) : ℝ := baseBump (R⁻¹ • x)

theorem baseBump_contDiff : ContDiff ℝ ∞ (fun x : Space => baseBump x) := baseBump.contDiff

theorem cutoff_contDiff (R : ℝ) : ContDiff ℝ ∞ (cutoff R) :=
  baseBump_contDiff.comp (contDiff_const_smul R⁻¹)

theorem cutoff_isSpatialTest {R : ℝ} (hR : 0 < R) : IsSpatialTest (cutoff R) :=
  ⟨cutoff_contDiff R, baseBump.hasCompactSupport.comp_smul (inv_ne_zero hR.ne')⟩

theorem cutoff_nonneg (R : ℝ) (x : Space) : 0 ≤ cutoff R x := baseBump.nonneg

theorem cutoff_le_one (R : ℝ) (x : Space) : cutoff R x ≤ 1 := baseBump.le_one

theorem abs_cutoff_le_one (R : ℝ) (x : Space) : |cutoff R x| ≤ 1 := by
  rw [abs_of_nonneg (cutoff_nonneg R x)]
  exact cutoff_le_one R x

theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : Space} (hx : ‖x‖ ≤ R) : cutoff R x = 1 := by
  apply baseBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_pos.2 hR).le]
  change R⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ hR, mul_one]
  exact hx

/-- A uniform bound for the derivative of the fixed bump. -/
theorem exists_fderiv_baseBump_bound :
    ∃ B, 0 ≤ B ∧ ∀ y : Space, ‖fderiv ℝ (fun x : Space => baseBump x) y‖ ≤ B := by
  obtain ⟨B, hB⟩ := (baseBump_contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (baseBump.hasCompactSupport.fderiv (𝕜 := ℝ))
  exact ⟨max B 0, le_max_right _ _, fun y => (hB y).trans (le_max_left _ _)⟩

/-- The chain rule for `χ_R`. -/
theorem spatialTestDerivative_cutoff (R : ℝ) (j : Fin 3) (x : Space) :
    spatialTestDerivative j (cutoff R) x =
      R⁻¹ * fderiv ℝ (fun y : Space => baseBump y) (R⁻¹ • x) (coordinateVector j) := by
  have hb : HasFDerivAt (fun y : Space => baseBump y)
      (fderiv ℝ (fun y : Space => baseBump y) (R⁻¹ • x)) (R⁻¹ • x) :=
    (baseBump_contDiff.differentiable (by simp) _).hasFDerivAt
  have hs : HasFDerivAt (fun y : Space => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ Space) x :=
    (hasFDerivAt_id x).const_smul R⁻¹
  have hc := hb.comp x hs
  unfold spatialTestDerivative
  change fderiv ℝ ((fun y : Space => baseBump y) ∘ fun y : Space => R⁻¹ • y) x _ = _
  rw [hc.fderiv]
  simp [smul_eq_mul]

theorem abs_spatialTestDerivative_cutoff_le {R B : ℝ} (hR : 0 < R)
    (hB : ∀ y : Space, ‖fderiv ℝ (fun x : Space => baseBump x) y‖ ≤ B) (j : Fin 3) (x : Space) :
    |spatialTestDerivative j (cutoff R) x| ≤ R⁻¹ * B := by
  rw [spatialTestDerivative_cutoff, abs_mul, abs_of_pos (inv_pos.2 hR)]
  apply mul_le_mul_of_nonneg_left _ (inv_pos.2 hR).le
  have h1 := (fderiv ℝ (fun y : Space => baseBump y) (R⁻¹ • x)).le_opNorm (coordinateVector j)
  have hn : ‖coordinateVector j‖ = 1 := by simp [coordinateVector]
  rw [hn, mul_one] at h1
  exact (Real.norm_eq_abs _ ▸ h1).trans (hB _)

/-! ## The cutoff sequence `R = n + 1` -/

theorem cutoff_tendsto_one (x : Space) :
    Tendsto (fun n : ℕ => cutoff ((n : ℝ) + 1) x) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  obtain ⟨m, hm⟩ := exists_nat_ge ‖x‖
  filter_upwards [eventually_ge_atTop m] with n hn
  refine (cutoff_eq_one (by positivity) ?_).symm
  have : (m : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem spatialTestDerivative_cutoff_tendsto_zero (j : Fin 3) (x : Space) :
    Tendsto (fun n : ℕ => spatialTestDerivative j (cutoff ((n : ℝ) + 1)) x) atTop (𝓝 0) := by
  simp_rw [spatialTestDerivative_cutoff]
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • x) atTop (𝓝 ((0 : ℝ) • x)) :=
    h1.smul_const x
  rw [zero_smul] at h2
  have h3 : Tendsto (fun n : ℕ => fderiv ℝ (fun y : Space => baseBump y) (((n : ℝ) + 1)⁻¹ • x)
      (coordinateVector j)) atTop
      (𝓝 (fderiv ℝ (fun y : Space => baseBump y) 0 (coordinateVector j))) :=
    (((baseBump_contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).tendsto 0).comp h2
  simpa using h1.mul h3

/-- `∫ χ_R f → ∫ f` for `f ∈ L¹`. -/
theorem tendsto_integral_cutoff_mul {f : Space → ℝ} (hf : Integrable f) :
    Tendsto (fun n : ℕ => ∫ x, cutoff ((n : ℝ) + 1) x * f x) atTop (𝓝 (∫ x, f x)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖) (fun n => ?_) hf.norm
    (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · exact ((cutoff_contDiff _).continuous.aestronglyMeasurable).mul hf.aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_cutoff_le_one _ _)
  · simpa using (cutoff_tendsto_one x).mul_const (f x)

/-- `∫ ∂ⱼχ_R f → 0` for `f ∈ L¹`. -/
theorem tendsto_integral_cutoff_deriv_mul {f : Space → ℝ} (hf : Integrable f) (j : Fin 3) :
    Tendsto (fun n : ℕ => ∫ x, spatialTestDerivative j (cutoff ((n : ℝ) + 1)) x * f x) atTop
      (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := exists_fderiv_baseBump_bound
  have h := tendsto_integral_of_dominated_convergence (fun x => B * ‖f x‖)
    (F := fun (n : ℕ) x => spatialTestDerivative j (cutoff ((n : ℝ) + 1)) x * f x)
    (f := fun _ => (0 : ℝ)) (fun n => ?_) (hf.norm.const_mul B)
    (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · simpa using h
  · exact (((cutoff_isSpatialTest (by positivity)).derivative j).smooth.continuous
      |>.aestronglyMeasurable).mul hf.aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine (abs_spatialTestDerivative_cutoff_le hR hB j x).trans ?_
    have : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
    nlinarith
  · simpa using (spatialTestDerivative_cutoff_tendsto_zero j x).mul_const (f x)

end UnforcedLeray.Blueprint.L14
