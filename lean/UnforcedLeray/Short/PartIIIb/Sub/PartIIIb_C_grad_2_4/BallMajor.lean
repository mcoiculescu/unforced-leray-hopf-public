import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2_4

/-!
# `PartIII-b:C/grad/2/4/3`: summable lattice majorant on the unit ball (exponent 5)

Source `the November 2 reference manuscript` lines 4973-4980. The Gaussian comparison
of `ball_geom` (`ReturnInst/PsipADiff/XPart.lean`), with exponent `3` replaced by `5`
(constant `4^5 = 1024`), and the summability of the shifted weighted Gaussian with exponent `5`.
-/

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Summability of `(1+|t - jc|)^5 e^{-α(t-jc)²}` over `j ∈ ℤ` (exponent-5 analogue of
`sp_poly4_summable`). -/
theorem bm_poly5_summable (t α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    Summable (fun j : ℤ => (1 + |t - (j : ℝ) * c|) ^ 5 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by
  have h0 := gp_gauss_summable t α c hα hc
  have h5 := gp_gauss_pow_summable t α c hα hc 5
  have hK : (0:ℝ) ≤ (1 + |t| + c) ^ 5 := pow_nonneg (by linarith [abs_nonneg t]) 5
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((h0.add h5).mul_left (16 * (1 + |t| + c) ^ 5))
  have hz : 0 ≤ |(j : ℝ)| := abs_nonneg _
  have hu : 1 + |t - (j : ℝ) * c| ≤ (1 + |t| + c) * (1 + |(j : ℝ)|) := by
    have h1 : |t - (j : ℝ) * c| ≤ |t| + |(j : ℝ)| * c := by
      have h2 := abs_sub t ((j : ℝ) * c)
      rw [abs_mul, abs_of_pos hc] at h2
      exact h2
    nlinarith [abs_nonneg t, mul_nonneg hz hc.le, mul_nonneg (abs_nonneg t) hz]
  have h1 : (1 + |t - (j : ℝ) * c|) ^ 5 ≤ (1 + |t| + c) ^ 5 * (1 + |(j : ℝ)|) ^ 5 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hu 5
  have h2 : (1 + |(j : ℝ)|) ^ 5 ≤ 16 * (1 + |(j : ℝ)| ^ 5) := by
    nlinarith [mul_nonneg (sq_nonneg (|(j : ℝ)| - 1))
      (by positivity : (0:ℝ) ≤ 15 * |(j : ℝ)| ^ 3 + 25 * |(j : ℝ)| ^ 2 + 25 * |(j : ℝ)| + 15)]
  have hE : 0 ≤ Real.exp (-α * (t - (j : ℝ) * c) ^ 2) := (Real.exp_pos _).le
  calc (1 + |t - (j : ℝ) * c|) ^ 5 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
      ≤ ((1 + |t| + c) ^ 5 * (16 * (1 + |(j : ℝ)| ^ 5))) *
          Real.exp (-α * (t - (j : ℝ) * c) ^ 2) :=
        mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 hK)) hE
    _ = 16 * (1 + |t| + c) ^ 5 * (Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
          + |(j : ℝ)| ^ 5 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by ring

theorem bm_ball5 (ν s : ℝ) (ha1 : 1 ≤ ageA ν s) (x z : ℝ × ℝ) (hz : ‖z - x‖ < 1) (j : ℤ) :
    (1 + ‖xj ν j z‖) ^ 5 * Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) ≤
      1024 * (1 + |x.2|) ^ 5 * Real.exp (1 / (4 * ageA ν s)) *
        ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 5 *
          Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
  have ha0 : 0 < ageA ν s := by linarith
  have hd1 : |z.1 - x.1| < 1 := by
    have := abs_fst_le' (z - x)
    simp only [Prod.fst_sub] at this
    linarith
  have hd2 : |z.2 - x.2| < 1 := by
    have := abs_snd_le' (z - x)
    simp only [Prod.snd_sub] at this
    linarith
  have hR := gp_one_add_norm ν j z
  have hz2 : 1 + |z.2| ≤ 2 * (1 + |x.2|) := by
    have := abs_sub_abs_le_abs_sub z.2 x.2
    linarith [abs_nonneg x.2]
  have hq1 : 1 + |z.1 - (j : ℝ) * cOf ν| ≤ 2 * (1 + |x.1 - (j : ℝ) * cOf ν|) := by
    have := abs_sub_abs_le_abs_sub (z.1 - (j : ℝ) * cOf ν) (x.1 - (j : ℝ) * cOf ν)
    have e : (z.1 - (j : ℝ) * cOf ν) - (x.1 - (j : ℝ) * cOf ν) = z.1 - x.1 := by ring
    rw [e] at this
    linarith [abs_nonneg (x.1 - (j : ℝ) * cOf ν)]
  have hR3 : (1 + ‖xj ν j z‖) ^ 5 ≤
      (2 * (1 + |x.2|) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν|))) ^ 5 := by
    apply pow_le_pow_left₀ (by positivity)
    exact le_trans hR (mul_le_mul hz2 hq1 (by positivity) (by positivity))
  have hE := gp_exp_le ν s ha0 j z
  have hdd := abs_lt.mp hd1
  have hq2 : (1 / (4 * ageA ν s)) * ((x.1 - (j : ℝ) * cOf ν) ^ 2 / 2 - 1)
      ≤ (1 / (4 * ageA ν s)) * (z.1 - (j : ℝ) * cOf ν) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [sq_nonneg ((x.1 - (j : ℝ) * cOf ν) + 2 * (z.1 - x.1)),
      mul_nonneg (by linarith [hdd.1, hdd.2] : (0:ℝ) ≤ 1 - (z.1 - x.1))
        (by linarith [hdd.1, hdd.2] : (0:ℝ) ≤ 1 + (z.1 - x.1))]
  have hE2 : Real.exp (-(1 / (4 * ageA ν s)) * (z.1 - (j : ℝ) * cOf ν) ^ 2)
      ≤ Real.exp (1 / (4 * ageA ν s)) *
        Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) := by
    have hw : 1 / (8 * ageA ν s) = 1 / (4 * ageA ν s) / 2 := by ring
    rw [← Real.exp_add, hw]
    apply Real.exp_le_exp.mpr
    nlinarith [hq2]
  have hEnn : 0 ≤ Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  calc (1 + ‖xj ν j z‖) ^ 5 * Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s))
      ≤ (2 * (1 + |x.2|) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν|))) ^ 5 *
          Real.exp (-(1 / (4 * ageA ν s)) * (z.1 - (j : ℝ) * cOf ν) ^ 2) :=
        mul_le_mul hR3 (hE) hEnn (by positivity)
    _ ≤ (2 * (1 + |x.2|) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν|))) ^ 5 *
          (Real.exp (1 / (4 * ageA ν s)) *
            Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) :=
        mul_le_mul_of_nonneg_left hE2 (by positivity)
    _ = 1024 * (1 + |x.2|) ^ 5 * Real.exp (1 / (4 * ageA ν s)) *
        ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 5 *
          Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
        ring

/-- The summable majorant of the exponent-5 Gaussian weights on the unit ball (generalises
`ubd_summable`/`ball_geom` to exponent `5`). -/
theorem pamxBallMajor : PAMXBallMajor := by
  unfold PAMXBallMajor
  intro ν hν s hs x C hC
  have ha0 : 0 < ageA ν s := by linarith
  have hα0 : 0 < 1 / (8 * ageA ν s) := by positivity
  have hc : 0 < cOf ν := by unfold cOf; positivity
  have hsum := (bm_poly5_summable x.1 (1 / (8 * ageA ν s)) (cOf ν) hα0 hc).mul_left
    (C * 1024 * (1 + |x.2|) ^ 5 * Real.exp (1 / (4 * ageA ν s)))
  refine ⟨fun j => C * 1024 * (1 + |x.2|) ^ 5 * Real.exp (1 / (4 * ageA ν s)) *
    ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 5 *
      Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)), hsum, ?_⟩
  intro j z hz
  have hb := mul_le_mul_of_nonneg_left (bm_ball5 ν s hs x z hz j) hC
  calc C * ((1 + ‖xj ν j z‖) ^ 5 * Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)))
      ≤ C * (1024 * (1 + |x.2|) ^ 5 * Real.exp (1 / (4 * ageA ν s)) *
          ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 5 *
            Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2))) := hb
    _ = C * 1024 * (1 + |x.2|) ^ 5 * Real.exp (1 / (4 * ageA ν s)) *
          ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 5 *
            Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
