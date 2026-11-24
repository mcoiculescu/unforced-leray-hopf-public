import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_2
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.GN
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APElliptic
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticC
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.Static

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- An `L^p` bound by `X` gives the integral bound `∫ ‖f‖^p ≤ X^p`. -/
theorem sl_int_pow_le {E : Type*} [NormedAddCommGroup E] {μ : Measure Plane} {f : Plane → E} {p X : ℝ} (hp : 0 < p) (hX : 0 ≤ X)
    (hf : MemLp f (ENNReal.ofReal p) μ) (h : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal X) :
    ∫ z, ‖f z‖ ^ p ∂μ ≤ X ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  have key := hf.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top
  rw [key, ENNReal.ofReal_le_ofReal_iff hX, ENNReal.toReal_ofReal hp.le] at h
  have hI : 0 ≤ ∫ z, ‖f z‖ ^ p ∂μ := integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hI _) h hp.le
  rwa [Real.rpow_inv_rpow hI hp.ne'] at h2

theorem sl_cube_third (a : ℝ) (ha : 0 ≤ a) : (a ^ (1/3 : ℝ)) ^ (3:ℝ) = a := by
  rw [← Real.rpow_mul ha]; norm_num

theorem sl_rpow_cube (y : ℝ) (hy : 0 ≤ y) : ((y ^ (1/2 : ℝ)) ^ (2/3 : ℝ)) ^ (3:ℝ) = y := by
  rw [← Real.rpow_mul (Real.rpow_nonneg hy _)]
  rw [← Real.rpow_mul hy]; norm_num

theorem sl_six_power (y : ℝ) (hy : 0 ≤ y) : ((y ^ (1/2 : ℝ)) ^ (1/3 : ℝ)) ^ (6:ℝ) = y ^ (1:ℝ) := by
  rw [← Real.rpow_mul (Real.rpow_nonneg hy _)]
  rw [← Real.rpow_mul hy]; norm_num

/-- Cube of a Hölder bound `T ≤ P^(1/3) S^(2/3)`. -/
theorem sl_cube_holder {T P S : ℝ} (hT : 0 ≤ T) (hP : 0 ≤ P) (hS : 0 ≤ S)
    (h : T ≤ P ^ (1/3 : ℝ) * S ^ (2/3 : ℝ)) : T ^ 3 ≤ P * S ^ 2 := by
  have h3 : (P ^ (1/3 : ℝ)) ^ 3 = P := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP]; norm_num
  have h2 : (S ^ (2/3 : ℝ)) ^ 3 = S ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS, ← Real.rpow_natCast]; norm_num
  calc T ^ 3 ≤ (P ^ (1/3 : ℝ) * S ^ (2/3 : ℝ)) ^ 3 := pow_le_pow_left₀ hT h 3
    _ = P * S ^ 2 := by rw [mul_pow, h3, h2]

/-- Fourth power of the second Hölder bound `S ≤ Q^(3/4) R^(1/4)`. -/
theorem sl_fourth_holder {S Q R : ℝ} (hS : 0 ≤ S) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (h : S ≤ Q ^ (3/4 : ℝ) * R ^ (1/4 : ℝ)) : S ^ 4 ≤ Q ^ 3 * R := by
  have h4 : (Q ^ (3/4 : ℝ)) ^ 4 = Q ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ]; norm_num
  have h1 : (R ^ (1/4 : ℝ)) ^ 4 = R := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR]; norm_num
  calc S ^ 4 ≤ (Q ^ (3/4 : ℝ) * R ^ (1/4 : ℝ)) ^ 4 := pow_le_pow_left₀ hS h 4
    _ = Q ^ 3 * R := by rw [mul_pow, h4, h1]

end UnforcedLeray.Short.PartI
