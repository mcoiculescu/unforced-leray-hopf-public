import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvGradKernel

/-!
# Leaf `PartII-b:T12/1/1/2/12`: decay of the gradient of the planar Newton potential of a test

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula);
classical Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a planar test `f` and `k ∈ {0,1}`, `|∂_k (N * f)(x)| ≤ C |x|⁻¹` for `|x|` large, since
`|∂_kN(z)| ≤ (2π)⁻¹ |z|⁻¹` and `|x - y| ≥ |x|/2` on the support of `f`
(`NewtonConvGradKernel`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- The gradient kernel satisfies `|∂_kN(z)| ≤ (2π)⁻¹ ‖z‖⁻¹` for every `z`. -/
theorem abs_newtonGradKernel_le_inv (k : Fin 2) (z : Pl) :
    |newtonGradKernel k z| ≤ (2 * Real.pi)⁻¹ * ‖z‖⁻¹ := by
  by_cases hz : z = 0
  · subst hz
    simp [newtonGradKernel]
  · have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hc : ∀ j : Fin 2, z j ^ 2 ≤ z 0 ^ 2 + z 1 ^ 2 := by
      have hc0 : z 0 ^ 2 ≤ z 0 ^ 2 + z 1 ^ 2 := by linarith [sq_nonneg (z 1)]
      have hc1 : z 1 ^ 2 ≤ z 0 ^ 2 + z 1 ^ 2 := by linarith [sq_nonneg (z 0)]
      intro j
      fin_cases j
      · exact hc0
      · exact hc1
    have hs0 : 0 ≤ z 0 ^ 2 + z 1 ^ 2 := by positivity
    have hnorm_le : ‖z‖ ≤ Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr ?_
      intro j
      rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt (hc j)
    have hsq : ‖z‖ ^ 2 ≤ z 0 ^ 2 + z 1 ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg z) hnorm_le 2
      rwa [Real.sq_sqrt hs0] at h
    have hs : 0 < z 0 ^ 2 + z 1 ^ 2 := lt_of_lt_of_le (pow_pos hnz 2) hsq
    have hfac : 0 < (2 * Real.pi)⁻¹ := by positivity
    have hk : |z k| ≤ ‖z‖ := by
      have := norm_le_pi_norm z k
      rwa [Real.norm_eq_abs] at this
    have hmain : |z k| / (z 0 ^ 2 + z 1 ^ 2) ≤ ‖z‖⁻¹ := by
      rw [div_le_iff₀ hs]
      calc |z k| ≤ ‖z‖ := hk
        _ = ‖z‖⁻¹ * ‖z‖ ^ 2 := by
          rw [sq, ← mul_assoc, inv_mul_cancel₀ hnz.ne', one_mul]
        _ ≤ ‖z‖⁻¹ * (z 0 ^ 2 + z 1 ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hnz.le)
    unfold newtonGradKernel
    rw [abs_div, abs_mul, abs_of_pos hfac, abs_of_pos hs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hmain hfac.le

/-- **Leaf `PartII-b:T12/1/1/2/12`.**  `|∂_k (N * f)(x)| ≤ C ‖x‖⁻¹` for `‖x‖` large, for a
planar test `f`. -/
theorem newtonConvGradDecay : NewtonConvGradDecay := by
  intro k f hf
  obtain ⟨ρ, hρ⟩ := hf.2.isCompact.isBounded.subset_closedBall 0
  have hfi : Integrable f volume := hf.1.continuous.integrable_of_hasCompactSupport hf.2
  refine ⟨Real.pi⁻¹ * ∫ y, |f y|, 2 * |ρ| + 1, fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := by linarith [abs_nonneg ρ]
  have hbd : ∀ y, ‖newtonGradKernel k (x - y) * f y‖ ≤ (Real.pi⁻¹ * ‖x‖⁻¹) * |f y| := by
    intro y
    by_cases hy : f y = 0
    · simp [hy]
    · have hyt : y ∈ tsupport f := subset_tsupport f hy
      have hy' : ‖y‖ ≤ |ρ| := by
        have h := hρ hyt
        rw [Metric.mem_closedBall, dist_zero_right] at h
        exact h.trans (le_abs_self ρ)
      have hsep : ‖x‖ / 2 ≤ ‖x - y‖ := by
        have h := norm_sub_norm_le x y
        linarith
      have hK2 : ‖x - y‖⁻¹ ≤ 2 * ‖x‖⁻¹ := by
        have h := inv_anti₀ (half_pos hxpos) hsep
        rw [inv_div, div_eq_mul_inv] at h
        exact h
      have hK := abs_newtonGradKernel_le_inv k (x - y)
      have hA : |newtonGradKernel k (x - y)| * |f y| ≤
          ((2 * Real.pi)⁻¹ * (2 * ‖x‖⁻¹)) * |f y| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact hK.trans (mul_le_mul_of_nonneg_left hK2 (by positivity))
      have hC : (2 * Real.pi)⁻¹ * (2 * ‖x‖⁻¹) = Real.pi⁻¹ * ‖x‖⁻¹ := by ring
      rw [hC] at hA
      rw [Real.norm_eq_abs, abs_mul]
      exact hA
  have hint := norm_integral_le_of_norm_le (hfi.abs.const_mul (Real.pi⁻¹ * ‖x‖⁻¹))
    (Eventually.of_forall hbd)
  rw [integral_const_mul] at hint
  rw [newtonConvGradKernel k f hf x]
  calc |∫ y, newtonGradKernel k (x - y) * f y|
      = ‖∫ y, newtonGradKernel k (x - y) * f y‖ := (Real.norm_eq_abs _).symm
    _ ≤ Real.pi⁻¹ * ‖x‖⁻¹ * ∫ y, |f y| := hint
    _ = (Real.pi⁻¹ * ∫ y, |f y|) * ‖x‖⁻¹ := by ring

end UnforcedLeray.Short.IIb.PlaneRiesz
