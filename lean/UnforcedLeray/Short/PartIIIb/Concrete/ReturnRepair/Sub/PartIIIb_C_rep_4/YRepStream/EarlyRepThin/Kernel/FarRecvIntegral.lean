import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.ThinRecv

/-!
# `farRecvIntegral` (source 5345-5352): the age integral is polynomial in `S`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Real identity: `s^{-3/2}(C (K/√s)^{-79/22})^2 = C^2 K^{-79/11} s^{23/11}` for `s > 0`. -/
theorem frr_real (C K s : ℝ) (hs : 0 < s) (hK : 0 < K) (hC : 0 ≤ C) :
    s ^ (-3 / 2 : ℝ) * (C * (K / Real.sqrt s) ^ (-(79 / 22 : ℝ))) ^ (2 : ℝ)
      = C ^ 2 * K ^ (-(79 / 11 : ℝ)) * s ^ (23 / 11 : ℝ) := by
  have hsq : Real.sqrt s = s ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow s
  have h2 : (K / Real.sqrt s) ^ (-(79 / 22 : ℝ)) = K ^ (-(79 / 22 : ℝ)) * s ^ (79 / 44 : ℝ) := by
    rw [Real.div_rpow hK.le (Real.sqrt_nonneg s), hsq, ← Real.rpow_mul hs.le, div_eq_mul_inv,
      ← Real.rpow_neg hs.le, show -(1 / 2 * -(79 / 22 : ℝ)) = (79 / 44 : ℝ) by norm_num]
  rw [h2, Real.mul_rpow hC (mul_nonneg (Real.rpow_nonneg hK.le _) (Real.rpow_nonneg hs.le _)),
    Real.mul_rpow (Real.rpow_nonneg hK.le _) (Real.rpow_nonneg hs.le _), Real.rpow_two,
    ← Real.rpow_mul hK.le, ← Real.rpow_mul hs.le]
  have e1 : -(79 / 22 : ℝ) * 2 = -(79 / 11 : ℝ) := by norm_num
  have e2 : (79 / 44 : ℝ) * 2 = 79 / 22 := by norm_num
  have e3 : s ^ (-3 / 2 : ℝ) * s ^ (79 / 22 : ℝ) = s ^ (23 / 11 : ℝ) := by
    rw [← Real.rpow_add hs]; norm_num
  rw [e1, e2]
  linear_combination (C ^ 2 * K ^ (-(79 / 11 : ℝ))) * e3

theorem farRecvIntegral : FarRecvIntegral := by
  intro S E C K F hS hE hC hK
  have hpt : ∀ s ∈ Ioo 0 S,
      ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * ENNReal.ofReal E ^ (2 : ℝ) *
        (ENNReal.ofReal (C * (K / Real.sqrt s) ^ (-(79 / 22 : ℝ))) * F) ^ (2 : ℝ)
        ≤ ENNReal.ofReal (E ^ 2 * (C ^ 2 * K ^ (-(79 / 11 : ℝ)) * S ^ (23 / 11 : ℝ))) *
            F ^ (2 : ℝ) := by
    intro s hs
    obtain ⟨hs0, hsS⟩ := hs
    have hA : 0 ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
    have hCc : 0 ≤ C * (K / Real.sqrt s) ^ (-(79 / 22 : ℝ)) :=
      mul_nonneg hC (Real.rpow_nonneg (div_nonneg hK.le (Real.sqrt_nonneg s)) _)
    have hle : C ^ 2 * K ^ (-(79 / 11 : ℝ)) * s ^ (23 / 11 : ℝ)
        ≤ C ^ 2 * K ^ (-(79 / 11 : ℝ)) * S ^ (23 / 11 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs0.le hsS.le (by norm_num))
        (mul_nonneg (sq_nonneg C) (Real.rpow_nonneg hK.le _))
    have hid := frr_real C K s hs0 hK hC
    have hL : ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * ENNReal.ofReal E ^ (2 : ℝ) *
        (ENNReal.ofReal (C * (K / Real.sqrt s) ^ (-(79 / 22 : ℝ))) * F) ^ (2 : ℝ)
        = ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * (C * (K / Real.sqrt s) ^ (-(79 / 22 : ℝ))) ^ (2 : ℝ)
            * E ^ 2) * F ^ (2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_rpow_of_nonneg hE (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg hCc (by norm_num), Real.rpow_two E,
        Real.rpow_two (C * (K / Real.sqrt s) ^ (-(79 / 22 : ℝ))),
        ENNReal.ofReal_mul (mul_nonneg hA (sq_nonneg _)), ENNReal.ofReal_mul hA]
      ring
    rw [hL]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    apply ENNReal.ofReal_le_ofReal
    have hX : s ^ (-3 / 2 : ℝ) * (C * (K / Real.sqrt s) ^ (-(79 / 22 : ℝ))) ^ (2 : ℝ) * E ^ 2
        = (C ^ 2 * K ^ (-(79 / 11 : ℝ)) * s ^ (23 / 11 : ℝ)) * E ^ 2 := by rw [hid]
    rw [hX]
    nlinarith [mul_le_mul_of_nonneg_left hle (sq_nonneg E)]
  refine le_trans (setLIntegral_mono' measurableSet_Ioo fun s hs => hpt s hs) ?_
  rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
  have hS34 : S ^ (34 / 11 : ℝ) = S ^ (23 / 11 : ℝ) * S := by
    rw [show (34 / 11 : ℝ) = 23 / 11 + 1 by norm_num, Real.rpow_add hS, Real.rpow_one]
  have hmul : ENNReal.ofReal (E ^ 2 * (C ^ 2 * K ^ (-(79 / 11 : ℝ)) * S ^ (23 / 11 : ℝ))) *
      ENNReal.ofReal S = ENNReal.ofReal (E ^ 2 * C ^ 2 * K ^ (-(79 / 11 : ℝ)) * S ^ (34 / 11 : ℝ)) := by
    rw [← ENNReal.ofReal_mul (by positivity), hS34]
    congr 1
    ring
  rw [mul_right_comm, hmul]
