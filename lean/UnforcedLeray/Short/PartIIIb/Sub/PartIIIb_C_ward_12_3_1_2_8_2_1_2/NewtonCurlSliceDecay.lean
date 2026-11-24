import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.NewtonVectorPotentialFarDeriv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.SpatialCurlSliceDerivBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.NewtonCurlSliceBoundNear

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/2/6`: global derivative decay of the Newton curl potential

Source `the November 2 reference manuscript` lines 1393-1400, 1409-1412.
Assembly only: the far bound `NewtonCurlSliceDecayFar` (from `newtonCurlSliceDecayFar_of`,
applied to the leaves `newtonVectorPotentialFarDeriv` and `spatialCurlSliceDerivBound`) and the
near bound `newtonCurlSliceBoundNear` at the far radius `ρ` combine into `NewtonCurlSliceDecay`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

/-- Far-field comparison `t^{-(k+2)} ≤ 16 (1+t)^{-(k+1)}` for `t ≥ 1`, `k ≤ 3`. -/
theorem newtonCurlFarAux (t : ℝ) (ht : 1 ≤ t) (k : ℕ) (hk : k ≤ 3) :
    t ^ (-((k : ℝ) + 2)) ≤ 16 * (1 + t) ^ (-((k : ℝ) + 1)) := by
  have h1 : t ^ (-((k : ℝ) + 2)) ≤ t ^ (-((k : ℝ) + 1)) :=
    Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have h2 : t ^ (-((k : ℝ) + 1)) ≤ 2 ^ (k + 1) * (1 + t) ^ (-((k : ℝ) + 1)) := by
    have e1 : t ^ (-((k : ℝ) + 1)) = (t ^ (k + 1))⁻¹ := by
      rw [show -((k : ℝ) + 1) = -(((k + 1 : ℕ)) : ℝ) by push_cast; ring,
        Real.rpow_neg (by linarith), Real.rpow_natCast]
    have e2 : (1 + t) ^ (-((k : ℝ) + 1)) = ((1 + t) ^ (k + 1))⁻¹ := by
      rw [show -((k : ℝ) + 1) = -(((k + 1 : ℕ)) : ℝ) by push_cast; ring,
        Real.rpow_neg (by linarith), Real.rpow_natCast]
    rw [e1, e2]
    have hpow : (1 + t) ^ (k + 1) ≤ 2 ^ (k + 1) * t ^ (k + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have hp0 : 0 < t ^ (k + 1) := by positivity
    have hq0 : 0 < (1 + t) ^ (k + 1) := by positivity
    rw [show (t ^ (k + 1))⁻¹ = 1 / t ^ (k + 1) by ring,
      show (2 : ℝ) ^ (k + 1) * ((1 + t) ^ (k + 1))⁻¹ = (2 : ℝ) ^ (k + 1) / (1 + t) ^ (k + 1) by ring,
      div_le_div_iff₀ hp0 hq0]
    linarith [hpow]
  have h3 : (2 : ℝ) ^ (k + 1) ≤ 16 := by
    have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this
    linarith
  have h4 : 0 ≤ (1 + t) ^ (-((k : ℝ) + 1)) := Real.rpow_nonneg (by linarith) _
  have h5 := mul_le_mul_of_nonneg_right h3 h4
  linarith

theorem newtonCurlSliceDecay : NewtonCurlSliceDecay := by
  intro P _ φ hφ
  obtain ⟨ρ, M1, hρ, hM1, hfar⟩ :=
    newtonCurlSliceDecayFar_of newtonVectorPotentialFarDeriv spatialCurlSliceDerivBound P φ hφ
  obtain ⟨M2, hM2, hnear⟩ := newtonCurlSliceBoundNear P φ hφ ρ
  have hR : 0 ≤ M2 * (1 + ρ) ^ 4 := mul_nonneg hM2 (by positivity)
  refine ⟨16 * M1 + M2 * (1 + ρ) ^ 4, by linarith, ?_⟩
  intro τ y k hk
  by_cases hy : ρ ≤ ‖y‖
  · have hA := hfar τ y hy k hk
    have hB := newtonCurlFarAux ‖y‖ (le_trans hρ hy) k hk
    have hW : 0 ≤ powWeight ((k : ℝ) + 1) y := (powWeight_pos _ _).le
    have hC : powWeight ((k : ℝ) + 1) y = (1 + ‖y‖) ^ (-((k : ℝ) + 1)) := rfl
    calc _ ≤ M1 * ‖y‖ ^ (-((k : ℝ) + 2)) := hA
      _ ≤ M1 * (16 * (1 + ‖y‖) ^ (-((k : ℝ) + 1))) := mul_le_mul_of_nonneg_left hB hM1
      _ = 16 * M1 * powWeight ((k : ℝ) + 1) y := by rw [hC]; ring
      _ ≤ (16 * M1 + M2 * (1 + ρ) ^ 4) * powWeight ((k : ℝ) + 1) y :=
          mul_le_mul_of_nonneg_right (by linarith) hW
  · push_neg at hy
    have hB := hnear τ y hy.le k hk
    have hX : ((1 + ρ) ^ (k + 1))⁻¹ ≤ powWeight ((k : ℝ) + 1) y := by
      rw [powWeight, show -((k : ℝ) + 1) = -(((k + 1 : ℕ)) : ℝ) by push_cast; ring,
        Real.rpow_neg (by positivity), Real.rpow_natCast]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) _)
    have hone : (1 : ℝ) ≤ (1 + ρ) ^ 4 * ((1 + ρ) ^ (k + 1))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_right₀ (by linarith) (by omega)
    have hmain : (1 : ℝ) ≤ (1 + ρ) ^ 4 * powWeight ((k : ℝ) + 1) y :=
      le_trans hone (mul_le_mul_of_nonneg_left hX (by positivity))
    calc _ ≤ M2 := hB
      _ ≤ M2 * ((1 + ρ) ^ 4 * powWeight ((k : ℝ) + 1) y) := le_mul_of_one_le_right hM2 hmain
      _ = M2 * (1 + ρ) ^ 4 * powWeight ((k : ℝ) + 1) y := by ring
      _ ≤ (16 * M1 + M2 * (1 + ρ) ^ 4) * powWeight ((k : ℝ) + 1) y :=
          mul_le_mul_of_nonneg_right (by linarith) (powWeight_pos _ _).le

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

end
