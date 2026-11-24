import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.Defs
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# `CutoffFamilyExists`

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
`χ n y = χ₀ (y/(n+1))` with one fixed `ContDiffBump` `χ₀` (`rIn = 1`, `rOut = 2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem cutoffFamilyExists_holds : CutoffFamilyExists := by
  let g : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ C := by
    have hcont : Continuous (fderiv ℝ g) := (g.contDiff (n := 1)).continuous_fderiv (by simp)
    obtain ⟨C, hC⟩ := (g.hasCompactSupport.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hcont
    exact ⟨C, hC⟩
  refine ⟨C, fun n => (fun y => g (((n : ℝ) + 1)⁻¹ • y)), fun n => ?_⟩
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hs : ContDiff ℝ ∞ (fun y : Space => ((n : ℝ) + 1)⁻¹ • y) := contDiff_const_smul _
  refine ⟨g.contDiff.comp hs, ?_, fun y => ⟨g.nonneg, g.le_one⟩, ?_, ?_, ?_⟩
  · have := g.hasCompactSupport
    refine this.comp_isClosedEmbedding ?_
    exact (Homeomorph.smulOfNeZero (((n : ℝ) + 1)⁻¹) (by positivity)).isClosedEmbedding
  · intro y hy
    apply g.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hn.le]
    show _ ≤ (1:ℝ)
    rw [inv_mul_le_iff₀ hn]; simpa using hy
  · intro y hy
    apply g.zero_of_le_dist
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hn.le]
    show 2 ≤ _
    rw [le_inv_mul_iff₀ hn]; linarith
  · intro y
    have hd : HasFDerivAt (fun y : Space => ((n : ℝ) + 1)⁻¹ • y)
        (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ Space) y :=
      (hasFDerivAt_id y).const_smul (((n : ℝ) + 1)⁻¹)
    have h1 := ((g.contDiff (n := 1)).differentiable (by simp) _).hasFDerivAt.comp y hd
    show ‖fderiv ℝ (fun y => g (((n : ℝ) + 1)⁻¹ • y)) y‖ ≤ _
    rw [show (fun y : Space => g (((n : ℝ) + 1)⁻¹ • y)) = g ∘ fun y : Space => ((n : ℝ) + 1)⁻¹ • y from rfl, h1.fderiv]
    calc _ ≤ ‖fderiv ℝ g (((n : ℝ) + 1)⁻¹ • y)‖ * ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ Space‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * ((n : ℝ) + 1)⁻¹ := by
          apply mul_le_mul (hC _) _ (norm_nonneg _) ((norm_nonneg _).trans (hC 0))
          rw [norm_smul, norm_inv, Real.norm_of_nonneg hn.le]
          calc _ ≤ ((n : ℝ) + 1)⁻¹ * 1 := by
                gcongr; exact ContinuousLinearMap.norm_id_le
            _ = _ := mul_one _
      _ = _ := by rw [div_eq_mul_inv, mul_comm]

end UnforcedLeray.Short.PartIIIb.Concrete
