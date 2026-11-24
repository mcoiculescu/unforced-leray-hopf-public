import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialSourceFamilyL1
import UnforcedLeray.Lib.CZL2.NewtonConv
import UnforcedLeray.Lib.CZL2.TestProjection

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.RieszLp

/-- Uniform Newton far-field bound for the actual real potential path. The source bounds are
obtained from the compact phase test itself, and the only spatial tail input is its common
compact support. -/
theorem exists_uniform_projectedPotentialRePath_far_bound {P : ℝ} [Fact (0 < P)]
    {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) :
    ∃ ρ C : ℝ, 0 ≤ ρ ∧ 0 ≤ C ∧
      ∀ τ ∈ Icc (0 : ℝ) P, ∀ y : Space, 2 * ρ ≤ ‖y‖ → y ≠ 0 →
        |projectedPotentialRePath Φ (τ, y)| ≤ C * (‖y‖ ^ 2)⁻¹ := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  let ρ := max R 0
  have hρ : 0 ≤ ρ := le_max_right _ _
  have hcoord : ∀ i : Fin 3, ∃ C : ℝ, 0 ≤ C ∧
      ∀ τ ∈ Icc (0 : ℝ) P, ∫ x, |projectedPotentialReTest Φ τ i x| ≤ C := by
    intro i
    exact exists_uniform_spatialL1_of_isPhaseTest
      (hΦ.clm_comp (projectedPotentialReCoordCLM i))
  choose C hC0 hC using hcoord
  refine ⟨ρ, Real.pi⁻¹ * ∑ i : Fin 3, C i, hρ, ?_, ?_⟩
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i hi => hC0 i)
  · intro τ hτ y hy hy0
    have hslice := isSpatialTest_projectedPotentialReTest hΦ τ
    rw [projectedPotentialRePath, lerayPotential_eq hslice y, abs_neg]
    have hsum : |∑ i : Fin 3, newtonPair i (projectedPotentialReTest Φ τ i) y| ≤
        ∑ i : Fin 3, Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ * C i := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro i hi
      have hsource : ∀ x, ρ < ‖x‖ → projectedPotentialReTest Φ τ i x = 0 := by
        intro x hx
        have hxR : R < ‖x‖ := lt_of_le_of_lt (le_max_left R 0) hx
        have hzero := hR τ x hxR
        simp [projectedPotentialReTest, hzero]
      have hfar := abs_newtonPair_le_of_far i
        ((hslice i).integrable) hsource (by linarith) hy0
      calc
        |newtonPair i (projectedPotentialReTest Φ τ i) y| ≤
            Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ *
              ∫ x, |projectedPotentialReTest Φ τ i x| := hfar
        _ ≤ Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ * C i := by
          gcongr
          exact hC i τ hτ
    have hsum' : ∑ i : Fin 3, Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ * C i =
        (Real.pi⁻¹ * ∑ i : Fin 3, C i) * (‖y‖ ^ 2)⁻¹ := by
      rw [show (∑ i : Fin 3, Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ * C i) =
        (Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹) * ∑ i : Fin 3, C i by
          rw [← Finset.mul_sum]]
      ring
    exact hsum.trans_eq hsum'

/-- Uniform Newton far-field bound for the actual imaginary potential path. -/
theorem exists_uniform_projectedPotentialImPath_far_bound {P : ℝ} [Fact (0 < P)]
    {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) :
    ∃ ρ C : ℝ, 0 ≤ ρ ∧ 0 ≤ C ∧
      ∀ τ ∈ Icc (0 : ℝ) P, ∀ y : Space, 2 * ρ ≤ ‖y‖ → y ≠ 0 →
        |projectedPotentialImPath Φ (τ, y)| ≤ C * (‖y‖ ^ 2)⁻¹ := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  let ρ := max R 0
  have hρ : 0 ≤ ρ := le_max_right _ _
  have hcoord : ∀ i : Fin 3, ∃ C : ℝ, 0 ≤ C ∧
      ∀ τ ∈ Icc (0 : ℝ) P, ∫ x, |projectedPotentialImTest Φ τ i x| ≤ C := by
    intro i
    exact exists_uniform_spatialL1_of_isPhaseTest
      (hΦ.clm_comp (projectedPotentialImCoordCLM i))
  choose C hC0 hC using hcoord
  refine ⟨ρ, Real.pi⁻¹ * ∑ i : Fin 3, C i, hρ, ?_, ?_⟩
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i hi => hC0 i)
  · intro τ hτ y hy hy0
    have hslice := isSpatialTest_projectedPotentialImTest hΦ τ
    rw [projectedPotentialImPath, lerayPotential_eq hslice y, abs_neg]
    have hsum : |∑ i : Fin 3, newtonPair i (projectedPotentialImTest Φ τ i) y| ≤
        ∑ i : Fin 3, Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ * C i := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro i hi
      have hsource : ∀ x, ρ < ‖x‖ → projectedPotentialImTest Φ τ i x = 0 := by
        intro x hx
        have hxR : R < ‖x‖ := lt_of_le_of_lt (le_max_left R 0) hx
        have hzero := hR τ x hxR
        simp [projectedPotentialImTest, hzero]
      have hfar := abs_newtonPair_le_of_far i
        ((hslice i).integrable) hsource (by linarith) hy0
      calc
        |newtonPair i (projectedPotentialImTest Φ τ i) y| ≤
            Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ *
              ∫ x, |projectedPotentialImTest Φ τ i x| := hfar
        _ ≤ Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ * C i := by
          gcongr
          exact hC i τ hτ
    have hsum' : ∑ i : Fin 3, Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ * C i =
        (Real.pi⁻¹ * ∑ i : Fin 3, C i) * (‖y‖ ^ 2)⁻¹ := by
      rw [show (∑ i : Fin 3, Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ * C i) =
        (Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹) * ∑ i : Fin 3, C i by
          rw [← Finset.mul_sum]]
      ring
    exact hsum.trans_eq hsum'

#print axioms exists_uniform_projectedPotentialRePath_far_bound
#print axioms exists_uniform_projectedPotentialImPath_far_bound

end UnforcedLeray.Cons.C03.Concrete

end
