import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Defs

/-!
# Part III-a, `PartIII-a:T21/2/2/2/6`: the equivalent periodic weight (SP 3044)

Proves `AdjWeightEquiv m` for `m > 8` (`m > 0` is all that is used):
`jb^{-m} ≤ p_d^{-m}` on the plane (from `|sin x| ≤ |x|`) and `p_d^{-m} ≤ (π²/4)^m jb^{-m}` on the
cell `|y₁| ≤ d/2` (from Jordan's inequality `2/π·x ≤ sin x` on `[0, π/2]`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- Lower bound on the periodic phase: `(4/π²) y₁² ≤ (d/π)² sin²(π y₁/d)` for `|y₁| ≤ d/2`. -/
theorem adjWeight_sinsq_aux (d y1 : ℝ) (hd : 0 < d) (hy : |y1| ≤ d / 2) :
    (4 / Real.pi ^ 2) * y1 ^ 2 ≤ (d / Real.pi) ^ 2 * Real.sin (Real.pi * y1 / d) ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx : |Real.pi * y1 / d| ≤ Real.pi / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos hd, div_le_iff₀ hd]
    nlinarith
  have hJ : 2 / Real.pi * |Real.pi * y1 / d| ≤ Real.sin |Real.pi * y1 / d| :=
    Real.mul_le_sin (abs_nonneg _) hx
  have h0 : 0 ≤ 2 / Real.pi * |Real.pi * y1 / d| := by positivity
  have hsq : Real.sin (Real.pi * y1 / d) ^ 2 = Real.sin |Real.pi * y1 / d| ^ 2 := by
    rcases le_total 0 (Real.pi * y1 / d) with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Real.sin_neg, neg_sq]
  have hkey : 4 / Real.pi ^ 2 * (Real.pi * y1 / d) ^ 2 ≤ Real.sin (Real.pi * y1 / d) ^ 2 := by
    rw [hsq]
    have h2 : (2 / Real.pi * |Real.pi * y1 / d|) ^ 2 ≤ Real.sin |Real.pi * y1 / d| ^ 2 :=
      pow_le_pow_left₀ h0 hJ 2
    have h3 : (2 / Real.pi * |Real.pi * y1 / d|) ^ 2 = 4 / Real.pi ^ 2 * |Real.pi * y1 / d| ^ 2 := by
      ring
    rw [sq_abs] at h3
    linarith
  have hx2 : (d / Real.pi) ^ 2 * (4 / Real.pi ^ 2 * (Real.pi * y1 / d) ^ 2) = 4 / Real.pi ^ 2 * y1 ^ 2 := by
    field_simp
  calc (4 / Real.pi ^ 2) * y1 ^ 2
      = (d / Real.pi) ^ 2 * (4 / Real.pi ^ 2 * (Real.pi * y1 / d) ^ 2) := hx2.symm
    _ ≤ (d / Real.pi) ^ 2 * Real.sin (Real.pi * y1 / d) ^ 2 :=
        mul_le_mul_of_nonneg_left hkey (sq_nonneg _)

/-- Upper bound on the phase: `(d/π)² sin²(π y₁/d) ≤ y₁²` for all `y₁`. -/
theorem adjWeight_sinsq_le (d y1 : ℝ) (hd : 0 < d) :
    (d / Real.pi) ^ 2 * Real.sin (Real.pi * y1 / d) ^ 2 ≤ y1 ^ 2 := by
  have h := Real.abs_sin_le_abs (x := Real.pi * y1 / d)
  have h2 := pow_le_pow_left₀ (abs_nonneg (Real.sin (Real.pi * y1 / d))) h 2
  rw [sq_abs, sq_abs] at h2
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hdne : d ≠ 0 := hd.ne'
  have hid : (d / Real.pi) ^ 2 * (Real.pi * y1 / d) ^ 2 = y1 ^ 2 := by
    field_simp
  calc (d / Real.pi) ^ 2 * Real.sin (Real.pi * y1 / d) ^ 2
      ≤ (d / Real.pi) ^ 2 * (Real.pi * y1 / d) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = y1 ^ 2 := hid

theorem adjWeightEquiv (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.E0.AdjWeightEquiv m := by
  intro d hd
  have hm0 : -m ≤ 0 := by linarith
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hc0 : (0 : ℝ) < 4 / Real.pi ^ 2 := by positivity
  have hcle : 4 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  constructor
  · intro y
    have hPpos : 0 < 1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 := by
      positivity
    have hle : 1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 ≤
        B0579.jb y := by
      have := adjWeight_sinsq_le d y.1 hd
      unfold B0579.jb
      linarith
    unfold periodicWeight
    exact Real.rpow_le_rpow_of_nonpos hPpos hle hm0
  · intro y hy
    have hy1 : |y.1| ≤ d / 2 := by
      have h1 : y.1 ∈ Ico (-(d / 2)) (d / 2) := hy.1
      exact abs_le.mpr ⟨h1.1, h1.2.le⟩
    have hsin := adjWeight_sinsq_aux d y.1 hd hy1
    have hjb : 0 < B0579.jb y := B0579.jb_pos y
    have hcj : 0 < (4 / Real.pi ^ 2) * B0579.jb y := mul_pos hc0 hjb
    have hcP : (4 / Real.pi ^ 2) * B0579.jb y ≤
        1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 := by
      unfold B0579.jb
      have hy2 : (4 / Real.pi ^ 2) * y.2 ^ 2 ≤ y.2 ^ 2 :=
        mul_le_of_le_one_left (sq_nonneg _) hcle
      nlinarith
    have hPpos : 0 < 1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 :=
      lt_of_lt_of_le hcj hcP
    have hc : (4 / Real.pi ^ 2) ^ (-m) = (Real.pi ^ 2 / 4) ^ m := by
      rw [Real.rpow_neg hc0.le, ← Real.inv_rpow hc0.le, inv_div]
    unfold periodicWeight
    calc (1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2) ^ (-m)
        ≤ ((4 / Real.pi ^ 2) * B0579.jb y) ^ (-m) :=
          Real.rpow_le_rpow_of_nonpos hcj hcP hm0
      _ = (4 / Real.pi ^ 2) ^ (-m) * B0579.jb y ^ (-m) :=
          Real.mul_rpow hc0.le hjb.le
      _ = (Real.pi ^ 2 / 4) ^ m * B0579.jb y ^ (-m) := by rw [hc]

end UnforcedLeray.Short.IIIa.E0
