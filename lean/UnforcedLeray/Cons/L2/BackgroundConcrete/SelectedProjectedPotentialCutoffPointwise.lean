import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialUniformPotentialTail
import UnforcedLeray.Lib.LerayLp.Cutoff

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.RieszLp
open NavierStokesR3.ComparisonCutoffs

/-- Uniform powWeight-three bound on each actual real-potential cutoff-shell coordinate. -/
theorem exists_uniform_projectedPotentialReCutoffShell_powWeight_bound
    {P : ℝ} [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) :
    ∃ R₀ K : ℝ, 0 < R₀ ∧ 0 ≤ K ∧
      ∀ R ≥ R₀, ∀ τ ∈ Icc (0 : ℝ) P, ∀ y : Space, ∀ i : Fin 3,
        |projectedPotentialRePath Φ (τ, y) *
          spatialTestDerivative i (cutoff R) y| ≤ K * powWeight 3 y := by
  obtain ⟨ρ, A, hρ, hA, hfar⟩ := exists_uniform_projectedPotentialRePath_far_bound hΦ
  let R₀ := max 1 (2 * ρ)
  have hR₀ : 0 < R₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨R₀, 12 * derivativeConstant 1 * A, hR₀,
    mul_nonneg (mul_nonneg (by norm_num) (derivativeConstant_pos 1).le) hA, ?_⟩
  intro R hR τ hτ y i
  have hderivbound := abs_spatialTestDerivative_cutoff_le (le_trans (le_max_left _ _) hR) y i
  by_cases hzero : spatialTestDerivative i (cutoff R) y = 0
  · simp [hzero]
    have hK : 0 ≤ 12 * derivativeConstant 1 * A :=
      mul_nonneg (mul_nonneg (by norm_num) (derivativeConstant_pos 1).le) hA
    exact mul_nonneg hK (powWeight_nonneg 3 y)
  have hRpos : 0 < R := lt_of_lt_of_le hR₀ hR
  have hRle : R ≤ ‖y‖ := by
    by_contra hn
    have hlt : ‖y‖ < R := lt_of_not_ge hn
    exact hzero (spatialTestDerivative_cutoff_of_lt hRpos hlt i)
  have hyfar : 2 * ρ ≤ ‖y‖ := le_trans (le_max_right 1 (2 * ρ)) (le_trans hR hRle)
  have hr1 : 1 ≤ ‖y‖ := le_trans (le_max_left 1 (2 * ρ)) (le_trans hR hRle)
  have hy0 : y ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hr1
    norm_num at hr1
  have hpot := hfar τ hτ y hyfar hy0
  have hderiv := abs_spatialTestDerivative_cutoff_le (le_trans (le_max_left _ _) hR) y i
  have hnormr : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hr1
  have hsq : (1 + ‖y‖) ^ 2 ≤ 4 * ‖y‖ ^ 2 := by nlinarith
  have hInv : (‖y‖ ^ 2)⁻¹ ≤ 4 * ((1 + ‖y‖) ^ 2)⁻¹ := by
    have hr2 : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hnormr)
    have hbr : (1 + ‖y‖) ^ 2 ≠ 0 := pow_ne_zero 2 (by positivity)
    field_simp
    nlinarith [hsq]
  have hprod : |projectedPotentialRePath Φ (τ, y) *
      spatialTestDerivative i (cutoff R) y| ≤
        (A * (‖y‖ ^ 2)⁻¹) * (3 * derivativeConstant 1 * (1 + ‖y‖)⁻¹) := by
    rw [abs_mul]
    exact mul_le_mul hpot hderiv (abs_nonneg _) (by positivity)
  rw [show powWeight 3 y = ((1 + ‖y‖) ^ (3 : ℕ))⁻¹ from
    powWeight_natCast (3 : ℕ) y]
  calc
    |projectedPotentialRePath Φ (τ, y) * spatialTestDerivative i (cutoff R) y| ≤
      (A * (‖y‖ ^ 2)⁻¹) * (3 * derivativeConstant 1 * (1 + ‖y‖)⁻¹) := hprod
    _ ≤ (12 * derivativeConstant 1 * A) * ((1 + ‖y‖) ^ (3 : ℕ))⁻¹ := by
      have hreplace : A * (‖y‖ ^ 2)⁻¹ ≤ A * (4 * ((1 + ‖y‖) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hInv hA
      calc
        (A * (‖y‖ ^ 2)⁻¹) * (3 * derivativeConstant 1 * (1 + ‖y‖)⁻¹) ≤
          (A * (4 * ((1 + ‖y‖) ^ 2)⁻¹)) *
            (3 * derivativeConstant 1 * (1 + ‖y‖)⁻¹) :=
              mul_le_mul_of_nonneg_right hreplace
                (mul_nonneg (mul_nonneg (by norm_num) (derivativeConstant_pos 1).le)
                  (inv_nonneg.mpr (by positivity)))
        _ = (12 * derivativeConstant 1 * A) * ((1 + ‖y‖) ^ (3 : ℕ))⁻¹ := by
              have hne : 1 + ‖y‖ ≠ 0 := by positivity
              field_simp [hne]
              ring

/-- The corresponding uniform bound for each actual imaginary-potential shell coordinate. -/
theorem exists_uniform_projectedPotentialImCutoffShell_powWeight_bound
    {P : ℝ} [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) :
    ∃ R₀ K : ℝ, 0 < R₀ ∧ 0 ≤ K ∧
      ∀ R ≥ R₀, ∀ τ ∈ Icc (0 : ℝ) P, ∀ y : Space, ∀ i : Fin 3,
        |projectedPotentialImPath Φ (τ, y) *
          spatialTestDerivative i (cutoff R) y| ≤ K * powWeight 3 y := by
  obtain ⟨ρ, A, hρ, hA, hfar⟩ := exists_uniform_projectedPotentialImPath_far_bound hΦ
  let R₀ := max 1 (2 * ρ)
  have hR₀ : 0 < R₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨R₀, 12 * derivativeConstant 1 * A, hR₀,
    mul_nonneg (mul_nonneg (by norm_num) (derivativeConstant_pos 1).le) hA, ?_⟩
  intro R hR τ hτ y i
  by_cases hzero : spatialTestDerivative i (cutoff R) y = 0
  · simp [hzero]
    have hK : 0 ≤ 12 * derivativeConstant 1 * A :=
      mul_nonneg (mul_nonneg (by norm_num) (derivativeConstant_pos 1).le) hA
    exact mul_nonneg hK (powWeight_nonneg 3 y)
  have hRpos : 0 < R := lt_of_lt_of_le hR₀ hR
  have hRle : R ≤ ‖y‖ := by
    by_contra hn
    have hlt : ‖y‖ < R := lt_of_not_ge hn
    exact hzero (spatialTestDerivative_cutoff_of_lt hRpos hlt i)
  have hyfar : 2 * ρ ≤ ‖y‖ := le_trans (le_max_right 1 (2 * ρ)) (le_trans hR hRle)
  have hr1 : 1 ≤ ‖y‖ := le_trans (le_max_left 1 (2 * ρ)) (le_trans hR hRle)
  have hy0 : y ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hr1
    norm_num at hr1
  have hpot := hfar τ hτ y hyfar hy0
  have hderiv := abs_spatialTestDerivative_cutoff_le (le_trans (le_max_left _ _) hR) y i
  have hnormr : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hr1
  have hsq : (1 + ‖y‖) ^ 2 ≤ 4 * ‖y‖ ^ 2 := by nlinarith
  have hInv : (‖y‖ ^ 2)⁻¹ ≤ 4 * ((1 + ‖y‖) ^ 2)⁻¹ := by
    have hr2 : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hnormr)
    have hbr : (1 + ‖y‖) ^ 2 ≠ 0 := pow_ne_zero 2 (by positivity)
    field_simp
    nlinarith [hsq]
  have hprod : |projectedPotentialImPath Φ (τ, y) *
      spatialTestDerivative i (cutoff R) y| ≤
        (A * (‖y‖ ^ 2)⁻¹) * (3 * derivativeConstant 1 * (1 + ‖y‖)⁻¹) := by
    rw [abs_mul]
    exact mul_le_mul hpot hderiv (abs_nonneg _) (by positivity)
  rw [show powWeight 3 y = ((1 + ‖y‖) ^ (3 : ℕ))⁻¹ from
    powWeight_natCast (3 : ℕ) y]
  calc
    |projectedPotentialImPath Φ (τ, y) * spatialTestDerivative i (cutoff R) y| ≤
      (A * (‖y‖ ^ 2)⁻¹) * (3 * derivativeConstant 1 * (1 + ‖y‖)⁻¹) := hprod
    _ ≤ (12 * derivativeConstant 1 * A) * ((1 + ‖y‖) ^ (3 : ℕ))⁻¹ := by
      have hreplace : A * (‖y‖ ^ 2)⁻¹ ≤ A * (4 * ((1 + ‖y‖) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hInv hA
      calc
        (A * (‖y‖ ^ 2)⁻¹) * (3 * derivativeConstant 1 * (1 + ‖y‖)⁻¹) ≤
          (A * (4 * ((1 + ‖y‖) ^ 2)⁻¹)) *
            (3 * derivativeConstant 1 * (1 + ‖y‖)⁻¹) :=
              mul_le_mul_of_nonneg_right hreplace
                (mul_nonneg (mul_nonneg (by norm_num) (derivativeConstant_pos 1).le)
                  (inv_nonneg.mpr (by positivity)))
        _ = (12 * derivativeConstant 1 * A) * ((1 + ‖y‖) ^ (3 : ℕ))⁻¹ := by
              have hne : 1 + ‖y‖ ≠ 0 := by positivity
              field_simp [hne]
              ring

#print axioms exists_uniform_projectedPotentialReCutoffShell_powWeight_bound
#print axioms exists_uniform_projectedPotentialImCutoffShell_powWeight_bound

end UnforcedLeray.Cons.C03.Concrete

end
