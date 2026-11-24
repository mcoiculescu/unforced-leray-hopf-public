import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Normed.Group.Real

/-!
# Mixed norms `L^p_τ L^∞_y` (INF14 target T9, mixed-norm part)


target T9 and risk 9: blueprint unit B0778 (tex 11083–11087) uses the mixed norm
`‖D^j X‖_{L²_τ L^∞_y}`. `L^∞` is not separable, so this is a mixed norm of a field `F(τ, y)`,
not the norm of an `L^∞`-valued Bochner function: `‖F‖ = ‖τ ↦ ‖F(τ, ·)‖_{L^∞}‖_{L^p}`.

## Main results

* `mixedNormLpLinf p ν μ F = eLpNorm (fun t => eLpNorm (F t) ∞ μ) p ν`;
* `mixedNormLpLinf_le_of_ae_bound`: a pointwise bound `|F(t, y)| ≤ g(t)` gives
  `‖F‖_{L^p L^∞} ≤ ‖g‖_{L^p}`;
* `mixedNormLpLinf_mono`: monotonicity under pointwise domination.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.BochnerTime

variable {τ α E E' : Type*} [MeasurableSpace τ] [MeasurableSpace α] [NormedAddCommGroup E]
  [NormedAddCommGroup E']

/-- The mixed norm `‖F‖_{L^p_τ L^∞_y}` of a field `F : τ → α → E` (B0778). -/
noncomputable def mixedNormLpLinf (p : ℝ≥0∞) (ν : Measure τ) (μ : Measure α) (F : τ → α → E) :
    ℝ≥0∞ :=
  eLpNorm (fun t => eLpNorm (F t) ∞ μ) p ν

/-- A bound `‖F(t, y)‖ ≤ g(t)` for a.e. `y`, for a.e. `t`, gives `‖F‖_{L^p L^∞} ≤ ‖g‖_{L^p}`. -/
theorem mixedNormLpLinf_le_of_ae_bound {p : ℝ≥0∞} {ν : Measure τ} {μ : Measure α}
    {F : τ → α → E} {g : τ → ℝ≥0∞} (h : ∀ᵐ t ∂ν, ∀ᵐ y ∂μ, ‖F t y‖ₑ ≤ g t) :
    mixedNormLpLinf p ν μ F ≤ eLpNorm g p ν := by
  unfold mixedNormLpLinf
  refine eLpNorm_mono_enorm_ae ?_
  filter_upwards [h] with t ht
  rw [enorm_eq_self, enorm_eq_self, eLpNorm_exponent_top]
  exact essSup_le_of_ae_le _ ht

/-- **Monotonicity.** If `‖F(t, y)‖ ≤ ‖G(t, y)‖` for a.e. `y`, for a.e. `t`, then
`‖F‖_{L^p L^∞} ≤ ‖G‖_{L^p L^∞}`. -/
theorem mixedNormLpLinf_mono {p : ℝ≥0∞} {ν : Measure τ} {μ : Measure α} {F : τ → α → E}
    {G : τ → α → E'} (h : ∀ᵐ t ∂ν, ∀ᵐ y ∂μ, ‖F t y‖ₑ ≤ ‖G t y‖ₑ) :
    mixedNormLpLinf p ν μ F ≤ mixedNormLpLinf p ν μ G := by
  unfold mixedNormLpLinf
  refine eLpNorm_mono_enorm_ae ?_
  filter_upwards [h] with t ht
  rw [enorm_eq_self, enorm_eq_self]
  exact eLpNorm_mono_enorm_ae ht

end UnforcedLeray.BochnerTime
