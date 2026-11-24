import UnforcedLeray.Analysis.Sturm.FreeResolventSelfAdjoint
import UnforcedLeray.Analysis.Sturm.ComplexPotentialMultiplier
import Mathlib.Tactic

/-!
# The actual Gaussian Birman--Schwinger operator

This is the explicit potential square-root multiplier on both sides of the
actual all-L² Green resolvent. Positivity and its quantitative norm bound
are consequences of those concrete operators; compactness is proved separately.
-/

noncomputable section
namespace UnforcedLeray.Sturm

/-- The actual square-root-potential/free-Green/square-root-potential sandwich. -/
def birmanSchwingerOperator {m : ℝ} (hm : 0 < m) : ComplexL2 →L[ℂ] ComplexL2 :=
  complexPotentialSqrtOperator.comp
    ((freeResolventOperator hm).comp complexPotentialSqrtOperator)

theorem birmanSchwingerOperator_apply {m : ℝ} (hm : 0 < m) (f : ComplexL2) :
    birmanSchwingerOperator hm f = complexPotentialSqrtOperator
      (freeResolventOperator hm (complexPotentialSqrtOperator f)) := rfl

/-- The concrete sandwich is a positive operator. -/
theorem birmanSchwingerOperator_isPositive {m : ℝ} (hm : 0 < m) :
    (birmanSchwingerOperator hm).IsPositive := by
  have h := (freeResolventOperator_isPositive hm).conj_adjoint
    complexPotentialSqrtOperator
  have hs := ContinuousLinearMap.isSelfAdjoint_iff'.mp
    complexPotentialSqrtOperator_isSelfAdjoint
  simpa only [hs, ContinuousLinearMap.comp_assoc, birmanSchwingerOperator] using h

theorem birmanSchwingerOperator_isSelfAdjoint {m : ℝ} (hm : 0 < m) :
    IsSelfAdjoint (birmanSchwingerOperator hm) :=
  (birmanSchwingerOperator_isPositive hm).isSelfAdjoint

/-- The upper endpoint estimate comes from actual Wlog ≤8 and the Green bound. -/
theorem norm_birmanSchwingerOperator_le {m : ℝ} (hm : 0 < m) :
    ‖birmanSchwingerOperator hm‖ ≤ 8 * (m ^ 2)⁻¹ := by
  calc
    ‖birmanSchwingerOperator hm‖ ≤ ‖complexPotentialSqrtOperator‖ *
        (‖freeResolventOperator hm‖ * ‖complexPotentialSqrtOperator‖) := by
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg _))
    _ ≤ Real.sqrt 8 * ((m ^ 2)⁻¹ * Real.sqrt 8) := by
      gcongr
      · exact norm_complexPotentialSqrtOperator_le
      · exact norm_freeResolventOperator_le hm
      · exact norm_complexPotentialSqrtOperator_le
    _ = 8 * (m ^ 2)⁻¹ := by
      calc
        _ = (Real.sqrt 8) ^ 2 * (m ^ 2)⁻¹ := by ring
        _ = _ := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)]

/-- At mass three the actual Birman--Schwinger norm is strictly less than one. -/
theorem norm_birmanSchwingerOperator_three_lt_one :
    ‖birmanSchwingerOperator (show (0 : ℝ) < 3 by norm_num)‖ < 1 := by
  have h := norm_birmanSchwingerOperator_le (show (0 : ℝ) < 3 by norm_num)
  norm_num at h
  linarith

end UnforcedLeray.Sturm
