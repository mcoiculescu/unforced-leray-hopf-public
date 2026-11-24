import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Lib.Gaussian.Periodization
import UnforcedLeray.Short.PartIIIa.Clock.Frame

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- Decay of the planar dual kernels in the `(1+|z₁|)^{-2}` form (source 2896-2899). -/
theorem perLam0_lam_bound (κ : IIIa.PlanarFrameKernels) (k : Fin 2) :
    ∃ A : ℝ, ∀ z : ℝ × ℝ, ‖κ.lamP k z‖ ≤ A * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC⟩ := κ.lamP_decay
  refine ⟨max C 0, fun z => ?_⟩
  have hq : (0 : ℝ) < 1 + |z.1| := by positivity
  have hle : 1 + |z.1| ≤ 1 + |z.1| + |z.2| := by linarith [abs_nonneg z.2]
  have hinv : (1 + |z.1| + |z.2|)⁻¹ ≤ (1 + |z.1|)⁻¹ := inv_anti₀ hq hle
  have hp : (1 + |z.1|) ^ (-(2 : ℝ)) = ((1 + |z.1|)⁻¹) ^ 2 := by
    rw [Real.rpow_neg hq.le, Real.rpow_two, inv_pow]
  calc ‖κ.lamP k z‖ ≤ max C 0 * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 :=
        (hC k z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    _ ≤ max C 0 * ((1 + |z.1|)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv 2) (le_max_right _ _)
    _ = max C 0 * (1 + |z.1|) ^ (-(2 : ℝ)) := by rw [hp]

/-- **The unnormalized periodized dual rows are continuous** (source 2896-2899). -/
theorem perLam0Continuous :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.PerLam0Continuous := by
  intro κ d k hd
  obtain ⟨A, hA⟩ := perLam0_lam_bound κ k
  have hfun : IIIa.perLam0 κ d k =
      fun y => ∑' n : ℤ, κ.lamP k (y - UnforcedLeray.Gaussian.shiftVec d n) := by
    funext y
    have hr := (Equiv.neg ℤ).tsum_eq
      (fun n : ℤ => κ.lamP k (y - UnforcedLeray.Gaussian.shiftVec d n))
    simp only [IIIa.perLam0, IIIa.perSum]
    rw [← hr]
    congr 1
    funext n
    congr 1
    ext <;> simp [UnforcedLeray.Gaussian.shiftVec]
  rw [hfun]
  exact UnforcedLeray.Gaussian.continuous_tsum_translates (κ.lamP_cont k)
    (by norm_num : (1 : ℝ) < 2) hd.ne' hA

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
