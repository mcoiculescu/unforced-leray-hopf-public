import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.
Pure real algebra.  With `P = p0² + p1²`, the drift part is bounded by `-4ζVP`, the
Hessian part by `-2νCθP` (sum of squares `Σ(ζH_kj + z_k p_j)²` and `|z|² ≤ Cθζ`), the
Laplacian and transport part by `-P(νCθ + V(1 + Cθ))` (using `|z_k| ≤ (1 + Cθ)/2`), and
`ζ ≤ 1` with `2νλ ≥ 5V + VCθ + 3νCθ` closes the bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- A real `w` with `w² ≤ Cθ` lies in `[-(1+Cθ)/2, (1+Cθ)/2]`. -/
theorem gradAlg_abs_aux (Cθ w : ℝ) (hCθ : 0 ≤ Cθ) (hw : w ^ 2 ≤ Cθ) :
    -((1 + Cθ) / 2) ≤ w ∧ w ≤ (1 + Cθ) / 2 := by
  have hm : Cθ ≤ ((1 + Cθ) / 2) ^ 2 := by nlinarith [sq_nonneg (1 - Cθ)]
  exact abs_le_of_sq_le_sq' (le_trans hw hm) (by linarith)

theorem gradAlg : UnforcedLeray.Short.IIb.GradAlg := by
  intro ν V Cθ lam ζ z0 z1 lz b0 b1 d00 d01 d10 d11 p0 p1 H00 H01 H10 H11
    hν hV hCθ hζ0 hζ1 hz hlz hb0 hb1 hd00 hd01 hd10 hd11 hlam
  have hP : 0 ≤ p0 ^ 2 + p1 ^ 2 := by positivity
  have hzC : z0 ^ 2 + z1 ^ 2 ≤ Cθ := le_trans hz (mul_le_of_le_one_right hCθ hζ1)
  have hlz' := abs_le.1 hlz
  have hb0' := abs_le.1 hb0
  have hb1' := abs_le.1 hb1
  have hd00' := abs_le.1 hd00
  have hd01' := abs_le.1 hd01
  have hd10' := abs_le.1 hd10
  have hd11' := abs_le.1 hd11
  -- drift part (without the factor ζ): 2(d00 p0² + d01 p0p1 + d10 p0p1 + d11 p1²) ≤ 4VP
  have hA : 0 ≤ 4 * V * (p0 ^ 2 + p1 ^ 2) -
      2 * (d00 * p0 ^ 2 + d01 * (p0 * p1) + d10 * (p0 * p1) + d11 * p1 ^ 2) := by
    linarith [mul_nonneg (by linarith [hd00'.2] : (0 : ℝ) ≤ V - d00) (sq_nonneg p0),
      mul_nonneg (by linarith [hd11'.2] : (0 : ℝ) ≤ V - d11) (sq_nonneg p1),
      mul_nonneg (by linarith [hd01'.2] : (0 : ℝ) ≤ V - d01) (sq_nonneg (p0 + p1)),
      mul_nonneg (by linarith [hd01'.1] : (0 : ℝ) ≤ V + d01) (sq_nonneg (p0 - p1)),
      mul_nonneg (by linarith [hd10'.2] : (0 : ℝ) ≤ V - d10) (sq_nonneg (p0 + p1)),
      mul_nonneg (by linarith [hd10'.1] : (0 : ℝ) ≤ V + d10) (sq_nonneg (p0 - p1))]
  -- Hessian and cross part: 2νζ|H|² + 4ν z·(Hp) + 2νCθ P ≥ 0
  have hB : 0 ≤ 2 * ν * ζ * (H00 ^ 2 + H10 ^ 2 + (H01 ^ 2 + H11 ^ 2)) +
      4 * ν * (z0 * (p0 * H00) + z0 * (p1 * H01) + z1 * (p0 * H10) + z1 * (p1 * H11)) +
      2 * ν * Cθ * (p0 ^ 2 + p1 ^ 2) := by
    rcases hζ0.eq_or_lt with h0 | hpos
    · subst h0
      have hz2 : z0 ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg z1, hz]) (sq_nonneg z0)
      have hz3 : z1 ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg z0, hz]) (sq_nonneg z1)
      have hz0 : z0 = 0 := (pow_eq_zero_iff two_ne_zero).1 hz2
      have hz1 : z1 = 0 := (pow_eq_zero_iff two_ne_zero).1 hz3
      subst hz0 hz1
      linarith [mul_nonneg (mul_nonneg hν.le hCθ) hP]
    · have hsq : 0 ≤ (ζ * H00 + z0 * p0) ^ 2 + (ζ * H01 + z0 * p1) ^ 2 +
          (ζ * H10 + z1 * p0) ^ 2 + (ζ * H11 + z1 * p1) ^ 2 := by positivity
      have hX : 0 ≤ ζ * (2 * ν * ζ * (H00 ^ 2 + H10 ^ 2 + (H01 ^ 2 + H11 ^ 2)) +
          4 * ν * (z0 * (p0 * H00) + z0 * (p1 * H01) + z1 * (p0 * H10) + z1 * (p1 * H11)) +
          2 * ν * Cθ * (p0 ^ 2 + p1 ^ 2)) := by
        linarith [mul_nonneg hν.le hsq, mul_nonneg (mul_nonneg hν.le hP) (sub_nonneg.2 hz)]
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_pos_of_neg hpos hneg
      linarith
  obtain ⟨hz0a, hz0b⟩ := gradAlg_abs_aux Cθ z0 hCθ (by linarith [sq_nonneg z1])
  obtain ⟨hz1a, hz1b⟩ := gradAlg_abs_aux Cθ z1 hCθ (by linarith [sq_nonneg z0])
  -- transport part: b·z + V(1 + Cθ) ≥ 0
  have hbz : 0 ≤ b0 * z0 + b1 * z1 + V * (1 + Cθ) := by
    linarith [mul_nonneg (by linarith [hb0'.1] : (0 : ℝ) ≤ V + b0)
        (by linarith : (0 : ℝ) ≤ (1 + Cθ) / 2 + z0),
      mul_nonneg (by linarith [hb0'.2] : (0 : ℝ) ≤ V - b0)
        (by linarith : (0 : ℝ) ≤ (1 + Cθ) / 2 - z0),
      mul_nonneg (by linarith [hb1'.1] : (0 : ℝ) ≤ V + b1)
        (by linarith : (0 : ℝ) ≤ (1 + Cθ) / 2 + z1),
      mul_nonneg (by linarith [hb1'.2] : (0 : ℝ) ≤ V - b1)
        (by linarith : (0 : ℝ) ≤ (1 + Cθ) / 2 - z1)]
  have hl : 0 ≤ ν * (lz + Cθ) := mul_nonneg hν.le (by linarith [hlz'.1])
  have hC : 0 ≤ (p0 ^ 2 + p1 ^ 2) *
      (ν * (lz + Cθ) + (b0 * z0 + b1 * z1 + V * (1 + Cθ))) :=
    mul_nonneg hP (by linarith)
  have hζVP : ζ * (V * (p0 ^ 2 + p1 ^ 2)) ≤ V * (p0 ^ 2 + p1 ^ 2) :=
    mul_le_of_le_one_left (mul_nonneg hV hP) hζ1
  have hA' := mul_nonneg hζ0 hA
  have hlamP : (5 * V + V * Cθ + 3 * ν * Cθ) * (p0 ^ 2 + p1 ^ 2) ≤
      (2 * ν * lam) * (p0 ^ 2 + p1 ^ 2) :=
    mul_le_mul_of_nonneg_right hlam hP
  linarith [hA', hB, hC, hlamP, hζVP]

end UnforcedLeray.Short.IIb
