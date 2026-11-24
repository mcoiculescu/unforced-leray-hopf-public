import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1_3

/-!
# `PartII-a:N01/9/1/3/3/2/1/3/2`: `HardySubst`

Source `the November 2 reference manuscript`
lines 1684-1689.  Change of variables `σ = t s` (`s > 0`) on `(0,s)` against `(0,1)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

theorem hardySubst : UnforcedLeray.Short.PartIIa.N01.HardySubst := by
  intro a ν s hν hs Φ hΦ
  have himg : (fun t : ℝ => s * t) '' Ioo (0:ℝ) 1 = Ioo 0 s := by
    rw [Set.image_mul_left_Ioo hs]; simp
  have hcov := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun t : ℝ => s * t)
    (f' := fun _ => s) (s := Ioo (0:ℝ) 1)
    (g := fun σ => ENNReal.ofReal (gradKernel a ν s σ) * Φ σ) measurableSet_Ioo
    (fun x _ => by simpa using ((hasDerivAt_id' x).const_mul s).hasDerivWithinAt)
    (fun x _ y _ hxy => mul_left_cancel₀ hs.ne' hxy)
  rw [himg, abs_of_pos hs] at hcov
  rw [hcov, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have key : s * gradKernel a ν s (s * t) =
      ν ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) * (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) := by
    have hs0 : s ≠ 0 := hs.ne'
    have ht0' : t ≠ 0 := ht0.ne'
    unfold gradKernel
    have e1 : s * t / s = t := by field_simp
    have e2 : ν * (s - s * t) = ν * s * (1 - t) := by ring
    rw [e1, e2, Real.mul_rpow (mul_nonneg hν.le hs.le) ht1.le, Real.mul_rpow hν.le hs.le,
      Real.rpow_sub_one ht0']
    field_simp
  have hk : ENNReal.ofReal s * ENNReal.ofReal (gradKernel a ν s (s * t)) =
      ENNReal.ofReal (ν ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) := by
    rw [← ENNReal.ofReal_mul hs.le, key,
      ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hν.le _) (Real.rpow_nonneg hs.le _))]
  calc ENNReal.ofReal s * (ENNReal.ofReal (gradKernel a ν s (s * t)) * Φ (s * t))
      = (ENNReal.ofReal s * ENNReal.ofReal (gradKernel a ν s (s * t))) * Φ (s * t) := by ring
    _ = (ENNReal.ofReal (ν ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ)))) * Φ (t * s) := by
          rw [hk, mul_comm s t]
    _ = ENNReal.ofReal (ν ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) *
        (ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) * Φ (t * s)) := by ring

end UnforcedLeray.Short.PartIIa.N01
