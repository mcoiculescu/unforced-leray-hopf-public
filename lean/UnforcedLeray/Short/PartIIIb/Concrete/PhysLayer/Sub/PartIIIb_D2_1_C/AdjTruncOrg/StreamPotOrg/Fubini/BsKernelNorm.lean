import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bsKernelNorm : BSKernelNorm := by
  intro w
  by_cases hw : w = 0
  · subst hw
    have h0 : bsKernel 0 = 0 := by
      ext i
      simp [bsKernel]
    simp [h0]
  · have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hcomp : ∀ i : Fin 3, ‖bsKernel w i‖ ^ 2
        = ((4 * Real.pi)⁻¹ * (‖w‖ ^ 3)⁻¹) ^ 2 * (w i) ^ 2 := by
      intro i
      simp only [bsKernel, PiLp.toLp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    have hsum : ∑ i, (w i) ^ 2 = ‖w‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    have key : ‖bsKernel w‖ ^ 2 = ((4 * Real.pi)⁻¹ * (‖w‖ ^ 2)⁻¹) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [hcomp]
      rw [← Finset.mul_sum, hsum]
      field_simp
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp key
end UnforcedLeray.Short.PartIIIb.Concrete
