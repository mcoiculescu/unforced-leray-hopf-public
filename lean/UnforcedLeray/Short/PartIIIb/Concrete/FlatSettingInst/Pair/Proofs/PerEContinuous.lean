import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Lib.Gaussian.Periodization
import UnforcedLeray.Short.PartIIIa.Clock.Frame

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- `(1 + |t|)^2 ≤ 16 exp(t^2/8)`. -/
theorem perE_one_add_sq_le_exp (t : ℝ) : (1 + |t|) ^ 2 ≤ 16 * Real.exp (t ^ 2 / 8) := by
  have h1 : |t| ^ 2 = t ^ 2 := sq_abs t
  have h2 : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
    nlinarith [sq_nonneg (|t| - 1)]
  have h3 : 1 + t ^ 2 / 8 ≤ Real.exp (t ^ 2 / 8) := by
    linarith [Real.add_one_le_exp (t ^ 2 / 8)]
  linarith

/-- Gaussian tail of the planar growing vector, in the `(1+|z₁|)^{-2}` form. -/
theorem perE_e_bound (κ : IIIa.PlanarFrameKernels) (k : Fin 2) :
    ∃ A : ℝ, ∀ z : ℝ × ℝ, ‖κ.e k z‖ ≤ A * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC⟩ := κ.e_decay
  refine ⟨16 * max C 0, fun z => ?_⟩
  have hpos : (0 : ℝ) < (1 + |z.1|) ^ 2 := by positivity
  have hp : (1 + |z.1|) ^ (-(2 : ℝ)) = ((1 + |z.1|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
  have h1 : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ Real.exp (-(z.1 ^ 2) / 8) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg z.2])
  have h2 : Real.exp (-(z.1 ^ 2) / 8) * Real.exp (z.1 ^ 2 / 8) = 1 := by
    rw [← Real.exp_add, show -(z.1 ^ 2) / 8 + z.1 ^ 2 / 8 = 0 by ring, Real.exp_zero]
  have h3 := perE_one_add_sq_le_exp z.1
  have h4 : Real.exp (-(z.1 ^ 2) / 8) * (1 + |z.1|) ^ 2 ≤ 16 := by
    calc Real.exp (-(z.1 ^ 2) / 8) * (1 + |z.1|) ^ 2
        ≤ Real.exp (-(z.1 ^ 2) / 8) * (16 * Real.exp (z.1 ^ 2 / 8)) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = 16 * (Real.exp (-(z.1 ^ 2) / 8) * Real.exp (z.1 ^ 2 / 8)) := by ring
      _ = 16 := by rw [h2]; ring
  have h5 : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ 16 / (1 + |z.1|) ^ 2 := by
    rw [le_div_iff₀ hpos]
    exact le_trans (mul_le_mul_of_nonneg_right h1 hpos.le) h4
  have hE : ‖κ.e k z‖ ≤ max C 0 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) :=
    (hC k z).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le)
  calc ‖κ.e k z‖ ≤ max C 0 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := hE
    _ ≤ max C 0 * (16 / (1 + |z.1|) ^ 2) :=
          mul_le_mul_of_nonneg_left h5 (le_max_right C 0)
    _ = 16 * max C 0 * (1 + |z.1|) ^ (-(2 : ℝ)) := by rw [hp]; ring

/-- **The periodized growing vectors are continuous** (source 2894-2899). -/
theorem perEContinuous :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.PerEContinuous := by
  intro κ d k hd
  obtain ⟨A, hA⟩ := perE_e_bound κ k
  have hfun : IIIa.perE κ d k =
      fun y => ∑' n : ℤ, κ.e k (y - UnforcedLeray.Gaussian.shiftVec d n) := by
    funext y
    have hr := (Equiv.neg ℤ).tsum_eq
      (fun n : ℤ => κ.e k (y - UnforcedLeray.Gaussian.shiftVec d n))
    simp only [IIIa.perE, IIIa.perSum]
    rw [← hr]
    congr 1
    funext n
    congr 1
    ext <;> simp [UnforcedLeray.Gaussian.shiftVec]
  rw [hfun]
  exact UnforcedLeray.Gaussian.continuous_tsum_translates (κ.e_cont k)
    (by norm_num : (1 : ℝ) < 2) hd.ne' hA

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
