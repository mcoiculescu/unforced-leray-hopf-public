import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.GradKL1

/-!
# `FmKerDom` (source 3604-3610, 3996-4011)

The heat-Leray gradient is dominated by the radial kernel `fmKer`: with `t = ν(1-l²)`,
`gradKNorm t w = ofReal (s^3 * s * gk1Sum 1 (s • w))` for `s = (√t)⁻¹` (`gk1_gsum_scale`), and
`gk1_bound` gives `gk1Sum 1 v ≤ K ((1+|v|)^4)⁻¹`.  Since `t^{-2} = s^4` and
`(1 + |w|/√t)^{-4} = ((1 + s|w|)^4)⁻¹`, the bound is `K · fmKer`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

theorem fmKerDom_aux (t : ℝ) (ht : 0 < t) (w : UnforcedLeray.Space) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ v : UnforcedLeray.Space, gk1Sum 1 v ≤ K * ((1 + ‖v‖) ^ 4)⁻¹) :
    gradKNorm t w ≤
      ENNReal.ofReal K * ENNReal.ofReal (t ^ (-2 : ℝ) * (1 + ‖w‖ / Real.sqrt t) ^ (-4 : ℝ)) := by
  have hsq0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs0 : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 hsq0
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hneg : ∀ x : ℝ, 0 ≤ x → ∀ n : ℕ, x ^ (-(n : ℝ)) = (x ^ n)⁻¹ := fun x hx n => by
    rw [Real.rpow_neg hx, Real.rpow_natCast]
  have e2 : (-2 : ℝ) = -((2 : ℕ) : ℝ) := by norm_num
  have e4 : (-4 : ℝ) = -((4 : ℕ) : ℝ) := by norm_num
  have h4 : Real.sqrt t ^ 4 = t ^ 2 := by
    calc Real.sqrt t ^ 4 = (Real.sqrt t ^ 2) ^ 2 := by ring
      _ = t ^ 2 := by rw [hsq]
  have hkey : t ^ (-2 : ℝ) * (1 + ‖w‖ / Real.sqrt t) ^ (-4 : ℝ)
      = (Real.sqrt t)⁻¹ ^ 4 * ((1 + (Real.sqrt t)⁻¹ * ‖w‖) ^ 4)⁻¹ := by
    rw [div_eq_inv_mul, e2, e4, hneg t ht.le 2,
      hneg (1 + (Real.sqrt t)⁻¹ * ‖w‖) (by positivity) 4, inv_pow, h4]
  have hf : (Real.sqrt t)⁻¹ ^ 3 * (Real.sqrt t)⁻¹ = (Real.sqrt t)⁻¹ ^ 4 := by ring
  have hnorm : ‖(Real.sqrt t)⁻¹ • w‖ = (Real.sqrt t)⁻¹ * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
  have hb' : gk1Sum 1 ((Real.sqrt t)⁻¹ • w) ≤ K * ((1 + (Real.sqrt t)⁻¹ * ‖w‖) ^ 4)⁻¹ := by
    have h := hb ((Real.sqrt t)⁻¹ • w)
    rwa [hnorm] at h
  rw [gk1_gradKNorm_eq, gk1_gsum_scale t ht w, hf, hkey, ← ENNReal.ofReal_mul hK]
  apply ENNReal.ofReal_le_ofReal
  calc (Real.sqrt t)⁻¹ ^ 4 * gk1Sum 1 ((Real.sqrt t)⁻¹ • w)
      ≤ (Real.sqrt t)⁻¹ ^ 4 * (K * ((1 + (Real.sqrt t)⁻¹ * ‖w‖) ^ 4)⁻¹) :=
        mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = K * ((Real.sqrt t)⁻¹ ^ 4 * ((1 + (Real.sqrt t)⁻¹ * ‖w‖) ^ 4)⁻¹) := by ring

theorem fmKerDom : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FmKerDom := by
  obtain ⟨K, hK, hb⟩ := gk1_bound
  refine ⟨K, hK, fun ν hν l hl w => ?_⟩
  have h1 : 0 < 1 - l ^ 2 :=
    by nlinarith [mul_pos (sub_pos.2 hl.2) (by linarith [hl.1] : (0 : ℝ) < 1 + l)]
  have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν h1
  unfold fmKer
  rw [if_pos hl]
  exact fmKerDom_aux _ ht w K hK hb

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
