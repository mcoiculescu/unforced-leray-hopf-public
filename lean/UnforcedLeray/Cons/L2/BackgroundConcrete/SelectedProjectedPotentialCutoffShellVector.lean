import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCutoffPointwise

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.RieszLp
open NavierStokesR3.ComparisonCutoffs

/-- The actual complex cutoff-shell field of the Newton-gradient correction. -/
def projectedPotentialNewtonCorrectionCutoffShellField (R : ℝ)
    (Φ : SpaceTime → CVec3) : SpaceTime → CVec3 := fun z =>
  ofReV (projectedPotentialRePath Φ z • gradField (cutoff R) z.2) +
    ofImV (projectedPotentialImPath Φ z • gradField (cutoff R) z.2)

/-- The actual complex cutoff shell has a uniform integrable spatial tail majorant. -/
theorem exists_uniform_projectedNewtonCorrectionCutoffShell_powWeight_bound
    {P : ℝ} [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) :
    ∃ R₀ K : ℝ, 0 < R₀ ∧ 0 ≤ K ∧
      ∀ R ≥ R₀, ∀ τ ∈ Icc (0 : ℝ) P, ∀ y : Space,
        ‖projectedPotentialNewtonCorrectionCutoffShellField R Φ (τ, y)‖ ≤
          K * powWeight 3 y := by
  obtain ⟨Rr, Kr, hRr, hKr, hcoordR⟩ :=
    exists_uniform_projectedPotentialReCutoffShell_powWeight_bound hΦ
  obtain ⟨Ri, Ki, hRi, hKi, hcoordI⟩ :=
    exists_uniform_projectedPotentialImCutoffShell_powWeight_bound hΦ
  let R₀ := max Rr Ri
  let K := 3 * (Kr + Ki)
  have hR₀ : 0 < R₀ := lt_of_lt_of_le hRr (le_max_left _ _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨R₀, K, hR₀, hK, ?_⟩
  intro R hR τ hτ y
  have hRrh : Rr ≤ R := le_trans (le_max_left _ _) hR
  have hRih : Ri ≤ R := le_trans (le_max_right _ _) hR
  have hRe : ∀ i : Fin 3,
      |projectedPotentialRePath Φ (τ, y) * spatialTestDerivative i (cutoff R) y| ≤
        Kr * powWeight 3 y := fun i => hcoordR R hRrh τ hτ y i
  have hIm : ∀ i : Fin 3,
      |projectedPotentialImPath Φ (τ, y) * spatialTestDerivative i (cutoff R) y| ≤
        Ki * powWeight 3 y := fun i => hcoordI R hRih τ hτ y i
  have hgradR : ‖projectedPotentialRePath Φ (τ, y) • gradField (cutoff R) y‖ ≤
      3 * Kr * powWeight 3 y := by
    have hdecomp : projectedPotentialRePath Φ (τ, y) • gradField (cutoff R) y =
        ∑ i : Fin 3,
          (projectedPotentialRePath Φ (τ, y) * spatialTestDerivative i (cutoff R) y) •
            coordinateVector i := by
      unfold gradField
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul]
    rw [hdecomp]
    calc
      ‖∑ i : Fin 3,
          (projectedPotentialRePath Φ (τ, y) * spatialTestDerivative i (cutoff R) y) •
            coordinateVector i‖ ≤
        ∑ i : Fin 3,
          |projectedPotentialRePath Φ (τ, y) * spatialTestDerivative i (cutoff R) y| :=
          norm_sum_smul_coordinateVector_le _
      _ ≤ ∑ _i : Fin 3, Kr * powWeight 3 y :=
        Finset.sum_le_sum fun i hi => hRe i
      _ = 3 * Kr * powWeight 3 y := by simp [Finset.sum_const, mul_assoc]
  have hgradI : ‖projectedPotentialImPath Φ (τ, y) • gradField (cutoff R) y‖ ≤
      3 * Ki * powWeight 3 y := by
    have hdecomp : projectedPotentialImPath Φ (τ, y) • gradField (cutoff R) y =
        ∑ i : Fin 3,
          (projectedPotentialImPath Φ (τ, y) * spatialTestDerivative i (cutoff R) y) •
            coordinateVector i := by
      unfold gradField
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul]
    rw [hdecomp]
    calc
      ‖∑ i : Fin 3,
          (projectedPotentialImPath Φ (τ, y) * spatialTestDerivative i (cutoff R) y) •
            coordinateVector i‖ ≤
        ∑ i : Fin 3,
          |projectedPotentialImPath Φ (τ, y) * spatialTestDerivative i (cutoff R) y| :=
          norm_sum_smul_coordinateVector_le _
      _ ≤ ∑ _i : Fin 3, Ki * powWeight 3 y :=
        Finset.sum_le_sum fun i hi => hIm i
      _ = 3 * Ki * powWeight 3 y := by simp [Finset.sum_const, mul_assoc]
  have hReEmb : ‖ofReV
      (projectedPotentialRePath Φ (τ, y) • gradField (cutoff R) y)‖ ≤
        3 * Kr * powWeight 3 y := by
    calc
      _ ≤ ‖ofReV‖ * ‖projectedPotentialRePath Φ (τ, y) • gradField (cutoff R) y‖ :=
        ofReV.le_opNorm _
      _ ≤ 1 * (3 * Kr * powWeight 3 y) :=
        mul_le_mul (norm_ofReV_le) hgradR (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hImEmb : ‖ofImV
      (projectedPotentialImPath Φ (τ, y) • gradField (cutoff R) y)‖ ≤
        3 * Ki * powWeight 3 y := by
    calc
      _ ≤ ‖ofImV‖ * ‖projectedPotentialImPath Φ (τ, y) • gradField (cutoff R) y‖ :=
        ofImV.le_opNorm _
      _ ≤ 1 * (3 * Ki * powWeight 3 y) :=
        mul_le_mul (norm_ofImV_le) hgradI (norm_nonneg _) (by positivity)
      _ = _ := by ring
  change ‖ofReV _ + ofImV _‖ ≤ K * powWeight 3 y
  calc
    ‖ofReV (projectedPotentialRePath Φ (τ, y) • gradField (cutoff R) y) +
        ofImV (projectedPotentialImPath Φ (τ, y) • gradField (cutoff R) y)‖ ≤
      ‖ofReV (projectedPotentialRePath Φ (τ, y) • gradField (cutoff R) y)‖ +
        ‖ofImV (projectedPotentialImPath Φ (τ, y) • gradField (cutoff R) y)‖ := norm_add_le _ _
    _ ≤ 3 * Kr * powWeight 3 y + 3 * Ki * powWeight 3 y := add_le_add hReEmb hImEmb
    _ = K * powWeight 3 y := by dsimp [K]; ring

#print axioms exists_uniform_projectedNewtonCorrectionCutoffShell_powWeight_bound

end UnforcedLeray.Cons.C03.Concrete

end
