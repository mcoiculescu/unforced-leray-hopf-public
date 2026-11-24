import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_8

/-!
# `PartIII-a:T21/2/2/2/5`: the weight bounds `AdjWeightBounds m`

Source: `the November 2 reference manuscript`, lines 3044-3050. The weight
`w = p_d^{-1} = periodicWeight (-m) d` with `p_d = Q_d^m`, `Q_d(y) = 1 + y₂² + (d/π)² sin²(πy₁/d)`.
The log-derivative bounds come from `PeriodicWeightLogBounds (-m)`; the `d`-derivative is computed
explicitly, `∂_d w = (-m) Q_d^{-m-1} ∂_d Q_d`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open UnforcedLeray.Short.IIIa
open UnforcedLeray.Short.IIIa.AdjE1 (pw_pos pw_contDiff pw_periodic pw_pd_abs_le pw_pd_eq)

namespace UnforcedLeray.Short.IIIa.E0

/-- The explicit `d`-derivative of `Q_d(y) = 1 + y₂² + (d/π)² sin²(πy₁/d)`. -/
def dQf (d : ℝ) (y : ℝ × ℝ) : ℝ :=
  2 * d / Real.pi ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 +
    (d / Real.pi) ^ 2 * (2 * Real.sin (Real.pi * y.1 / d) * Real.cos (Real.pi * y.1 / d) *
      (-(Real.pi * y.1) / d ^ 2))

theorem Qf_hasDerivAt (d : ℝ) (hd : 0 < d) (y : ℝ × ℝ) :
    HasDerivAt (fun t => WLB.Qf t y) (dQf d y) d := by
  have hs : HasDerivAt (fun t : ℝ => Real.sin (Real.pi * y.1 / t))
      (Real.cos (Real.pi * y.1 / d) * (-(Real.pi * y.1) / d ^ 2)) d := by
    have hinv : HasDerivAt (fun t : ℝ => Real.pi * y.1 / t) (-(Real.pi * y.1) / d ^ 2) d := by
      have h := (hasDerivAt_const d (Real.pi * y.1)).div (hasDerivAt_id d) hd.ne'
      refine h.congr_deriv ?_
      simp only [id]
      ring
    exact hinv.sin
  have hp : HasDerivAt (fun t : ℝ => (t / Real.pi) ^ 2) (2 * d / Real.pi ^ 2) d := by
    have h := ((hasDerivAt_id d).div_const Real.pi).pow 2
    refine h.congr_deriv ?_
    norm_num [id]
    field_simp
  have hq := (hasDerivAt_const d (1 + y.2 ^ 2)).add (hp.mul (hs.pow 2))
  have hf : HasDerivAt (fun t => WLB.Qf t y) (0 + (2 * d / Real.pi ^ 2 *
      Real.sin (Real.pi * y.1 / d) ^ 2 + (d / Real.pi) ^ 2 *
      (↑(2 : ℕ) * Real.sin (Real.pi * y.1 / d) ^ (2 - 1) *
        (Real.cos (Real.pi * y.1 / d) * (-(Real.pi * y.1) / d ^ 2))))) d := hq
  refine hf.congr_deriv ?_
  unfold dQf
  rw [show (2:ℕ) - 1 = 1 from rfl, pow_one, zero_add]
  push_cast
  ring

theorem pw_hasDerivAt_d (m d : ℝ) (hd : 0 < d) (y : ℝ × ℝ) :
    HasDerivAt (fun t => periodicWeight m t y) (m * WLB.Qf d y ^ (m - 1) * dQf d y) d := by
  have h := (Qf_hasDerivAt d hd y).rpow_const (p := m) (Or.inl (WLB.Qf_pos d y).ne')
  exact h.congr_deriv (by ring)

theorem wDd_eq (m d : ℝ) (hd : 0 < d) (y : ℝ × ℝ) :
    wDd m d y = (-m) * WLB.Qf d y ^ (-m - 1) * dQf d y := by
  unfold wDd
  exact (pw_hasDerivAt_d (-m) d hd y).deriv

theorem wDd_eq_mul (m d : ℝ) (hd : 0 < d) (y : ℝ × ℝ) :
    wDd m d y = periodicWeight (-m) d y *
      deriv (fun d' => Real.log (periodicWeight (-m) d' y)) d := by
  have hdiff : DifferentiableAt ℝ (fun t => periodicWeight (-m) t y) d :=
    (pw_hasDerivAt_d (-m) d hd y).differentiableAt
  have hl := deriv.log hdiff (pw_pos (-m) d y).ne'
  have hw0 : periodicWeight (-m) d y ≠ 0 := (pw_pos (-m) d y).ne'
  unfold wDd
  rw [hl]
  field_simp

theorem adjWeightBounds (m : ℝ) (hm : 8 < m) (hW : PeriodicWeightLogBounds) :
    UnforcedLeray.Short.IIIa.E0.AdjWeightBounds m := by
  obtain ⟨C, hC⟩ := hW (-m)
  refine ⟨|C|, abs_nonneg C, fun d hd => ?_⟩
  obtain ⟨hC1, _hC2, hC3, hC4⟩ := hC d hd
  have hwnn : ∀ y : ℝ × ℝ, 0 ≤ periodicWeight (-m) d y := fun y => (pw_pos (-m) d y).le
  refine
    { base := ?_, dil := ?_, dlen := ?_, dlenCont := ?_ }
  · refine
      { smooth := ?_, periodic := ?_, nonneg := hwnn, grad := ?_ }
    · exact (pw_contDiff (-m) d).of_le (by simp)
    · intro y
      exact pw_periodic (-m) d hd.ne' y
    · intro y k
      exact le_trans (pw_pd_abs_le (-m) d C (fun y k => hC1 y k) k y)
        (mul_le_mul_of_nonneg_right (le_abs_self C) (hwnn y))
  · intro y hy
    unfold wDil
    rw [pw_pd_eq (-m) d 0 y, pw_pd_eq (-m) d 1 y]
    have e : y.1 * (periodicWeight (-m) d y * B0579.pd 0 (fun x => Real.log (periodicWeight (-m) d x)) y)
        + y.2 * (periodicWeight (-m) d y * B0579.pd 1 (fun x => Real.log (periodicWeight (-m) d x)) y)
        = periodicWeight (-m) d y * (y.1 * B0579.pd 0 (fun x => Real.log (periodicWeight (-m) d x)) y
          + y.2 * B0579.pd 1 (fun x => Real.log (periodicWeight (-m) d x)) y) := by ring
    rw [e, abs_mul, abs_of_nonneg (hwnn y)]
    calc periodicWeight (-m) d y * |y.1 * B0579.pd 0 (fun x => Real.log (periodicWeight (-m) d x)) y
          + y.2 * B0579.pd 1 (fun x => Real.log (periodicWeight (-m) d x)) y|
        ≤ periodicWeight (-m) d y * C := mul_le_mul_of_nonneg_left (hC3 y hy) (hwnn y)
      _ ≤ periodicWeight (-m) d y * |C| :=
          mul_le_mul_of_nonneg_left (le_abs_self C) (hwnn y)
      _ = |C| * periodicWeight (-m) d y := by ring
  · intro y hy
    rw [wDd_eq_mul m d hd y]
    have e : d * (periodicWeight (-m) d y *
        deriv (fun d' => Real.log (periodicWeight (-m) d' y)) d)
        = periodicWeight (-m) d y * (d * deriv (fun d' => Real.log (periodicWeight (-m) d' y)) d) := by
      ring
    rw [e, abs_mul, abs_of_nonneg (hwnn y)]
    calc periodicWeight (-m) d y * |d * deriv (fun d' => Real.log (periodicWeight (-m) d' y)) d|
        ≤ periodicWeight (-m) d y * C := mul_le_mul_of_nonneg_left (hC4 y hy) (hwnn y)
      _ ≤ periodicWeight (-m) d y * |C| :=
          mul_le_mul_of_nonneg_left (le_abs_self C) (hwnn y)
      _ = |C| * periodicWeight (-m) d y := by ring
  · have hfun : wDd m d = fun y => (-m) * WLB.Qf d y ^ (-m - 1) * dQf d y :=
      funext (fun y => wDd_eq m d hd y)
    rw [hfun]
    have hQc : Continuous (fun y => WLB.Qf d y) := by
      unfold WLB.Qf
      fun_prop
    have hQpow : Continuous (fun y => WLB.Qf d y ^ (-m - 1)) :=
      hQc.rpow_const (fun y => Or.inl (WLB.Qf_pos d y).ne')
    have hdQ : Continuous (dQf d) := by
      unfold dQf
      fun_prop
    exact (continuous_const.mul hQpow).mul hdQ

end UnforcedLeray.Short.IIIa.E0
