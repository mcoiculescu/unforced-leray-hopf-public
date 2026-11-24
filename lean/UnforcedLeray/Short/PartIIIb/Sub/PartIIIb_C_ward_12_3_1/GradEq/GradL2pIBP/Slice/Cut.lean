import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP.IBPCS

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.GradSlice

open MeasureTheory Set Filter Topology

/-- Spatial cutoffs `χ_n = f(x/(n+1))` with a uniform gradient bound `C/(n+1)`. -/
theorem exists_cutoff : ∃ C : ℝ, 0 ≤ C ∧ ∃ χ : ℕ → EuclideanSpace ℝ (Fin 3) → ℝ,
    (∀ n, ContDiff ℝ 1 (χ n)) ∧ (∀ n, HasCompactSupport (χ n)) ∧
    (∀ n y, 0 ≤ χ n y ∧ χ n y ≤ 1) ∧
    (∀ y, Tendsto (fun n => χ n y) atTop (nhds 1)) ∧
    (∀ n y v, ‖fderiv ℝ (χ n) y v‖ ≤ C * ‖v‖ / ((n : ℝ) + 1)) := by
  let f : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) := ⟨1, 2, one_pos, one_lt_two⟩
  have hfc : ContDiff ℝ 1 (f : EuclideanSpace ℝ (Fin 3) → ℝ) := f.contDiff
  have hdf : Continuous (fun y => fderiv ℝ (f : EuclideanSpace ℝ (Fin 3) → ℝ) y) :=
    hfc.continuous_fderiv one_ne_zero
  have hcs : HasCompactSupport (fun y => fderiv ℝ (f : EuclideanSpace ℝ (Fin 3) → ℝ) y) :=
    f.hasCompactSupport.fderiv (𝕜 := ℝ)
  obtain ⟨C, hC⟩ := hdf.norm.bounded_above_of_compact_support hcs.norm
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, hC0, fun n y => f (((n : ℝ) + 1)⁻¹ • y), ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hfc.comp (contDiff_const_smul _)
  · intro n
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    have := f.hasCompactSupport.comp_homeomorph
      ((Homeomorph.smulOfNeZero (((n : ℝ) + 1)⁻¹) (by simpa using hn)))
    exact this
  · intro n y
    exact ⟨f.nonneg, f.le_one⟩
  · intro y
    refine tendsto_const_nhds.congr' ?_
    have : ∀ᶠ n : ℕ in atTop, ‖y‖ ≤ (n : ℝ) + 1 := by
      filter_upwards [eventually_ge_atTop ⌈‖y‖⌉₊] with n hn
      have := Nat.le_ceil ‖y‖
      have h2 : (⌈‖y‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    filter_upwards [this] with n hn
    symm
    apply f.one_of_mem_closedBall
    have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hp]
    show ((n : ℝ) + 1)⁻¹ * ‖y‖ ≤ 1
    rw [inv_mul_le_iff₀ hp]; linarith
  · intro n y v
    have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hd : DifferentiableAt ℝ (f : EuclideanSpace ℝ (Fin 3) → ℝ) (((n : ℝ) + 1)⁻¹ • y) :=
      (hfc.differentiable one_ne_zero) _
    have : fderiv ℝ (fun y => f (((n : ℝ) + 1)⁻¹ • y)) y
        = (fderiv ℝ (f : EuclideanSpace ℝ (Fin 3) → ℝ) (((n : ℝ) + 1)⁻¹ • y)).comp
            (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ _) := by
      have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => ((n : ℝ) + 1)⁻¹ • y)
          (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))) y :=
        by
          have := (hasFDerivAt_id (𝕜 := ℝ) y).const_smul (((n : ℝ) + 1)⁻¹)
          exact this
      exact (hd.hasFDerivAt.comp y h1).fderiv
    rw [this]
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hp]
    calc ((n : ℝ) + 1)⁻¹ * ‖fderiv ℝ (f : EuclideanSpace ℝ (Fin 3) → ℝ) (((n : ℝ) + 1)⁻¹ • y) v‖
        ≤ ((n : ℝ) + 1)⁻¹ * (C * ‖v‖) := by
          gcongr
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (by simpa using hC _) (norm_nonneg v))
      _ = C * ‖v‖ / ((n : ℝ) + 1) := by field_simp

end UnforcedLeray.Short.PartIIIb.Concrete.GradSlice
