import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2.HpADiffS
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.XPart
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.Phi
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.SPart

/-!
# `PartIII-b:C/grad/2/3`: `y ↦ ∂_η ψ^p_A(s, y)` is differentiable (second `x`-derivative)

Source `the November 2 reference manuscript` lines 4973-4980 (`ψ^p_A = Σ_j Φ(x_j)`,
"the sums and their required derivatives converge by Gaussian decay"), 4741-4745, 5081-5084.

`∂_ηΦ = E · (a⁻² R + a⁻³ S)` with `E = e^{-|y|²/(4a)}`, `R` linear and `S` cubic in `y`.  The
directional derivative of this along `w` is bounded by `10 K ‖w‖ (1+|y|)^4 E`; on a unit ball the
terms are dominated by a summable Gaussian majorant, and `hasFDerivAt_tsum_of_isPreconnected`
differentiates the sum.  First `fderiv ψ^p_A y (0,1) = Σ_j ∂_ηΦ(x_j(y))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## Closed form of `∂_η Φ` and of its directional derivative -/

def pxR (M : Mat3) (y : ℝ × ℝ) : ℝ := y.2 * (M 0 0 - M 2 2) - y.1 * (M 0 2 + M 2 0)

def pxQ (M : Mat3) (y : ℝ × ℝ) : ℝ :=
  M 0 0 * y.1 ^ 2 + (M 0 2 + M 2 0) * y.1 * y.2 + M 2 2 * y.2 ^ 2

def pxS (M : Mat3) (y : ℝ × ℝ) : ℝ := y.2 * pxQ M y / 2

/-- Derivative of `pxQ` along `w`. -/
def pxQd (M : Mat3) (y w : ℝ × ℝ) : ℝ :=
  2 * M 0 0 * y.1 * w.1 + (M 0 2 + M 2 0) * (w.1 * y.2 + y.1 * w.2) + 2 * M 2 2 * y.2 * w.2

/-- Derivative of `pxS` along `w`. -/
def pxSd (M : Mat3) (y w : ℝ × ℝ) : ℝ := (w.2 * pxQ M y + y.2 * pxQd M y w) / 2

/-- Directional derivative of `y ↦ E (a⁻² R + a⁻³ S)` along `w`. -/
def pxD (ν s : ℝ) (M : Mat3) (y w : ℝ × ℝ) : ℝ :=
  Real.exp (-(sq2 y) / (4 * ageA ν s)) *
    ((-(2 * y.1 * w.1 + 2 * y.2 * w.2) / (4 * ageA ν s)) *
        ((ageA ν s)⁻¹ * (ageA ν s)⁻¹ * pxR M y + (ageA ν s)⁻¹ * (ageA ν s)⁻¹ * (ageA ν s)⁻¹ * pxS M y)
      + ((ageA ν s)⁻¹ * (ageA ν s)⁻¹ * pxR M w
        + (ageA ν s)⁻¹ * (ageA ν s)⁻¹ * (ageA ν s)⁻¹ * pxSd M y w))

theorem px_psiPhiD_e2 (ν t : ℝ) (M : Mat3) (y : ℝ × ℝ) :
    psiPhiD ν t M y (0, 1) = Real.exp (-(sq2 y) / (4 * ageA ν t)) *
      ((ageA ν t)⁻¹ * (ageA ν t)⁻¹ * pxR M y
        + (ageA ν t)⁻¹ * (ageA ν t)⁻¹ * (ageA ν t)⁻¹ * pxS M y) := by
  by_cases ha : ageA ν t = 0
  · simp [psiPhiD, ha]
  · unfold psiPhiD pxR pxS pxQ merApply merTrace
    dsimp only
    field_simp
    ring

theorem px_line (ν s : ℝ) (M : Mat3) (y w : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => psiPhiD ν s M (y + t • w) (0, 1)) (pxD ν s M y w) 0 := by
  have hc1 : HasDerivAt (fun t : ℝ => y.1 + t * w.1) w.1 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const w.1).const_add y.1
  have hc2 : HasDerivAt (fun t : ℝ => y.2 + t * w.2) w.2 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const w.2).const_add y.2
  have hfun : (fun t : ℝ => psiPhiD ν s M (y + t • w) (0, 1)) = fun t : ℝ =>
      Real.exp (-((y.1 + t * w.1) * (y.1 + t * w.1) + (y.2 + t * w.2) * (y.2 + t * w.2))
          / (4 * ageA ν s)) *
        ((ageA ν s)⁻¹ * (ageA ν s)⁻¹ *
            ((y.2 + t * w.2) * (M 0 0 - M 2 2) - (y.1 + t * w.1) * (M 0 2 + M 2 0))
          + (ageA ν s)⁻¹ * (ageA ν s)⁻¹ * (ageA ν s)⁻¹ *
            ((y.2 + t * w.2) * (M 0 0 * (y.1 + t * w.1) ^ 2
              + (M 0 2 + M 2 0) * (y.1 + t * w.1) * (y.2 + t * w.2)
              + M 2 2 * (y.2 + t * w.2) ^ 2) / 2)) := by
    funext t
    rw [px_psiPhiD_e2]
    simp only [pxR, pxS, pxQ, sq2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring_nf
  rw [hfun]
  have hg : HasDerivAt (fun t : ℝ =>
      -((y.1 + t * w.1) * (y.1 + t * w.1) + (y.2 + t * w.2) * (y.2 + t * w.2))
        / (4 * ageA ν s)) (-(2 * y.1 * w.1 + 2 * y.2 * w.2) / (4 * ageA ν s)) 0 := by
    have := (((hc1.mul hc1).add (hc2.mul hc2)).neg.div_const (4 * ageA ν s))
    refine this.congr_deriv ?_
    simp only [add_zero, zero_mul, mul_zero]
    ring
  have hE := hg.exp
  have hRt : HasDerivAt (fun t : ℝ =>
      (y.2 + t * w.2) * (M 0 0 - M 2 2) - (y.1 + t * w.1) * (M 0 2 + M 2 0))
      (w.2 * (M 0 0 - M 2 2) - w.1 * (M 0 2 + M 2 0)) 0 :=
    (hc2.mul_const _).sub (hc1.mul_const _)
  have hQt : HasDerivAt (fun t : ℝ => M 0 0 * (y.1 + t * w.1) ^ 2
      + (M 0 2 + M 2 0) * (y.1 + t * w.1) * (y.2 + t * w.2) + M 2 2 * (y.2 + t * w.2) ^ 2)
      (M 0 0 * (2 * (y.1 + 0 * w.1) * w.1) + (M 0 2 + M 2 0) * (w.1 * (y.2 + 0 * w.2)
        + (y.1 + 0 * w.1) * w.2) + M 2 2 * (2 * (y.2 + 0 * w.2) * w.2)) 0 := by
    have a1 := (hc1.pow 2).const_mul (M 0 0)
    have a2 := ((hc1.const_mul (M 0 2 + M 2 0)).mul hc2)
    have a3 := (hc2.pow 2).const_mul (M 2 2)
    have := (a1.add a2).add a3
    refine this.congr_deriv ?_
    simp only [add_zero, zero_mul, mul_zero, Nat.cast_ofNat]
    ring
  have hSt := (hc2.mul hQt).div_const 2
  have hu : (ageA ν s)⁻¹ * (ageA ν s)⁻¹ = (ageA ν s)⁻¹ * (ageA ν s)⁻¹ := rfl
  have hF := hE.mul ((hRt.const_mul ((ageA ν s)⁻¹ * (ageA ν s)⁻¹)).add
    (hSt.const_mul ((ageA ν s)⁻¹ * (ageA ν s)⁻¹ * (ageA ν s)⁻¹)))
  refine hF.congr_deriv ?_
  simp only [Pi.add_apply, Pi.mul_apply, pxD, pxR, pxSd, pxS, pxQ, pxQd, sq2, add_zero, zero_mul, mul_zero, zero_smul]
  ring

/-! ## The real bound -/

theorem px_real_bound (a E K R n y1 y2 w1 w2 m00 m02 m20 m22 : ℝ) (ha : 1 ≤ a) (hE : 0 ≤ E)
    (hR : 0 ≤ R) (hn : 0 ≤ n) (hy1 : |y1| ≤ R) (hy2 : |y2| ≤ R) (hw1 : |w1| ≤ n)
    (hw2 : |w2| ≤ n) (h00 : |m00| ≤ K) (h02 : |m02| ≤ K) (h20 : |m20| ≤ K) (h22 : |m22| ≤ K) :
    let Rv := y2 * (m00 - m22) - y1 * (m02 + m20)
    let Q := m00 * y1 ^ 2 + (m02 + m20) * y1 * y2 + m22 * y2 ^ 2
    let Qd := 2 * m00 * y1 * w1 + (m02 + m20) * (w1 * y2 + y1 * w2) + 2 * m22 * y2 * w2
    let Rw := w2 * (m00 - m22) - w1 * (m02 + m20)
    let Sv := y2 * Q / 2
    let Sd := (w2 * Q + y2 * Qd) / 2
    |E * ((-(2 * y1 * w1 + 2 * y2 * w2) / (4 * a)) *
        (a⁻¹ * a⁻¹ * Rv + a⁻¹ * a⁻¹ * a⁻¹ * Sv) + (a⁻¹ * a⁻¹ * Rw + a⁻¹ * a⁻¹ * a⁻¹ * Sd))|
      ≤ E * (10 * K * n * (1 + R) ^ 4) := by
  intro Rv Q Qd Rw Sv Sd
  have hK : 0 ≤ K := (abs_nonneg _).trans h00
  have ha0 : 0 < a := by linarith
  have h4a : 0 < 4 * a := by linarith
  have hu0 : 0 < a⁻¹ := inv_pos.mpr ha0
  have hu1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
  have huu0 : 0 ≤ a⁻¹ * a⁻¹ := by positivity
  have huu1 : a⁻¹ * a⁻¹ ≤ 1 := by nlinarith
  have huuu0 : 0 ≤ a⁻¹ * a⁻¹ * a⁻¹ := by positivity
  have huuu1 : a⁻¹ * a⁻¹ * a⁻¹ ≤ 1 := by nlinarith
  have hs1 : |m00 - m22| ≤ 2 * K := (abs_sub _ _).trans (by linarith)
  have hs2 : |m02 + m20| ≤ 2 * K := (abs_add_le _ _).trans (by linarith)
  have hy1s : |y1 ^ 2| ≤ R ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hy1 2
  have hy2s : |y2 ^ 2| ≤ R ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hy2 2
  -- Rv, Rw
  have bRv : |Rv| ≤ 4 * K * R := by
    have t1 := abs_mul_le2 hy2 hs1
    have t2 := abs_mul_le2 hy1 hs2
    have := abs_sub (y2 * (m00 - m22)) (y1 * (m02 + m20))
    show |y2 * (m00 - m22) - y1 * (m02 + m20)| ≤ _
    nlinarith
  have bRw : |Rw| ≤ 4 * K * n := by
    have t1 := abs_mul_le2 hw2 hs1
    have t2 := abs_mul_le2 hw1 hs2
    have := abs_sub (w2 * (m00 - m22)) (w1 * (m02 + m20))
    show |w2 * (m00 - m22) - w1 * (m02 + m20)| ≤ _
    nlinarith
  -- Q
  have bQ : |Q| ≤ 4 * K * R ^ 2 := by
    have t1 := abs_mul_le2 h00 hy1s
    have t2 := abs_mul_le2 (abs_mul_le2 hs2 hy1) hy2
    have t3 := abs_mul_le2 h22 hy2s
    have s1 := abs_add_le (m00 * y1 ^ 2 + (m02 + m20) * y1 * y2) (m22 * y2 ^ 2)
    have s2 := abs_add_le (m00 * y1 ^ 2) ((m02 + m20) * y1 * y2)
    show |m00 * y1 ^ 2 + (m02 + m20) * y1 * y2 + m22 * y2 ^ 2| ≤ _
    nlinarith
  have bSv : |Sv| ≤ 2 * K * R ^ 3 := by
    have t := abs_mul_le2 hy2 bQ
    show |y2 * Q / 2| ≤ _
    rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith
  have two : ∀ m y w : ℝ, |m| ≤ K → |y| ≤ R → |w| ≤ n → |2 * m * y * w| ≤ 2 * K * R * n := by
    intro m y w hm hy hw
    have h2m : |2 * m| ≤ 2 * K := by rw [abs_mul, abs_two]; linarith
    have := abs_mul_le2 (abs_mul_le2 h2m hy) hw
    linarith
  have bQd : |Qd| ≤ 8 * K * R * n := by
    have t1 := two m00 y1 w1 h00 hy1 hw1
    have t3 := two m22 y2 w2 h22 hy2 hw2
    have hc : |w1 * y2 + y1 * w2| ≤ 2 * (R * n) := by
      have a1 := abs_mul_le2 hw1 hy2
      have a2 := abs_mul_le2 hy1 hw2
      have := abs_add_le (w1 * y2) (y1 * w2)
      nlinarith
    have t2 := abs_mul_le2 hs2 hc
    have s1 := abs_add_le (2 * m00 * y1 * w1 + (m02 + m20) * (w1 * y2 + y1 * w2))
      (2 * m22 * y2 * w2)
    have s2 := abs_add_le (2 * m00 * y1 * w1) ((m02 + m20) * (w1 * y2 + y1 * w2))
    show |2 * m00 * y1 * w1 + (m02 + m20) * (w1 * y2 + y1 * w2) + 2 * m22 * y2 * w2| ≤ _
    nlinarith
  have bSd : |Sd| ≤ 6 * K * R ^ 2 * n := by
    have t1 := abs_mul_le2 hw2 bQ
    have t2 := abs_mul_le2 hy2 bQd
    have s := abs_add_le (w2 * Q) (y2 * Qd)
    show |(w2 * Q + y2 * Qd) / 2| ≤ _
    rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith
  have hg : |-(2 * y1 * w1 + 2 * y2 * w2) / (4 * a)| ≤ R * n := by
    rw [abs_div, abs_neg, abs_of_pos h4a, div_le_iff₀ h4a]
    have h1 := abs_mul_le2 hy1 hw1
    have h2 := abs_mul_le2 hy2 hw2
    have e1 : |2 * y1 * w1| = 2 * |y1 * w1| := by rw [mul_assoc, abs_mul, abs_two]
    have e2 : |2 * y2 * w2| = 2 * |y2 * w2| := by rw [mul_assoc, abs_mul, abs_two]
    have := abs_add_le (2 * y1 * w1) (2 * y2 * w2)
    nlinarith [mul_nonneg hR hn, mul_nonneg (mul_nonneg hR hn) (sub_nonneg.2 ha)]
  have i1 : |a⁻¹ * a⁻¹ * Rv + a⁻¹ * a⁻¹ * a⁻¹ * Sv| ≤ 4 * K * R + 2 * K * R ^ 3 :=
    (abs_add_le _ _).trans (add_le_add (abs_pmul_le huu0 huu1 bRv) (abs_pmul_le huuu0 huuu1 bSv))
  have i2 : |a⁻¹ * a⁻¹ * Rw + a⁻¹ * a⁻¹ * a⁻¹ * Sd| ≤ 4 * K * n + 6 * K * R ^ 2 * n :=
    (abs_add_le _ _).trans (add_le_add (abs_pmul_le huu0 huu1 bRw) (abs_pmul_le huuu0 huuu1 bSd))
  have j1 := abs_mul_le2 hg i1
  have j2 := (abs_add_le _ _).trans (add_le_add j1 i2)
  rw [abs_mul, abs_of_nonneg hE]
  refine mul_le_mul_of_nonneg_left (j2.trans ?_) hE
  have hKn : 0 ≤ K * n := mul_nonneg hK hn
  have hp : 0 ≤ 6 + 40 * R + 50 * R ^ 2 + 40 * R ^ 3 + 8 * R ^ 4 := by positivity
  nlinarith [mul_nonneg hKn hp]

/-- Gaussian comparison on the unit ball: `(1+|x_j(z)|)³ e^{-|x_j(z)|²/(4a)}` is dominated
by `64(1+|x_2|)³ e^{1/(4a)} (1+|q_j|)³ e^{-q_j²/(8a)}` for `q_j = x_1 - jc`. -/
theorem ball_geom4 (ν s : ℝ) (ha1 : 1 ≤ ageA ν s) (x z : ℝ × ℝ) (hz : ‖z - x‖ < 1) (j : ℤ) :
    (1 + ‖xj ν j z‖) ^ 4 * Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) ≤
      256 * (1 + |x.2|) ^ 4 * Real.exp (1 / (4 * ageA ν s)) *
        ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 4 *
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
  have hR3 : (1 + ‖xj ν j z‖) ^ 4 ≤
      (2 * (1 + |x.2|) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν|))) ^ 4 := by
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
  calc (1 + ‖xj ν j z‖) ^ 4 * Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s))
      ≤ (2 * (1 + |x.2|) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν|))) ^ 4 *
          Real.exp (-(1 / (4 * ageA ν s)) * (z.1 - (j : ℝ) * cOf ν) ^ 2) :=
        mul_le_mul hR3 (hE) hEnn (by positivity)
    _ ≤ (2 * (1 + |x.2|) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν|))) ^ 4 *
          (Real.exp (1 / (4 * ageA ν s)) *
            Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) :=
        mul_le_mul_of_nonneg_left hE2 (by positivity)
    _ = 256 * (1 + |x.2|) ^ 4 * Real.exp (1 / (4 * ageA ν s)) *
        ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 4 *
          Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
        ring


/-! ## First `x`-derivative of the sum, as a sum -/

theorem psiPhi_tsum_hasFDerivAt (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (M : Mat3) (x : ℝ × ℝ) :
    HasFDerivAt (fun z => ∑' n : ℤ, psiPhi ν s M (xj ν n z))
      (∑' n : ℤ, fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) x) x ∧
    Summable (fun n : ℤ => fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) x) := by
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hu := ubd_summable ν s ha1 x M hν
  have hval : ∀ (j : ℤ) (z : ℝ × ℝ), ‖z - x‖ < 1 → ∀ v : ℝ × ℝ,
      ‖psiPhiD ν s M (xj ν j z) v‖ ≤ ubd ν s x M j * ‖v‖ := by
    intro j z hz v
    have h1 := psiPhiD_bound ν s ha1 M (xj ν j z) v
    have h2 := ball_geom ν s ha1 x z hz j
    have hn := norm_nonneg v
    have h6 : 0 ≤ 6 * Kmat M := by have := Kmat_nonneg M; linarith
    have h3 : 6 * Kmat M * ‖v‖ * ((1 + ‖xj ν j z‖) ^ 3 *
        Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)))
        ≤ 6 * Kmat M * ‖v‖ * (64 * (1 + |x.2|) ^ 3 * Real.exp (1 / (4 * ageA ν s)) *
          ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
            Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2))) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg h6 hn)
    refine h1.trans (h3.trans (le_of_eq ?_))
    unfold ubd
    ring
  have hfb : ∀ (j : ℤ) (z : ℝ × ℝ), ‖z - x‖ < 1 →
      ‖fderiv ℝ (fun w => psiPhi ν s M (xj ν j w)) z‖ ≤ ubd ν s x M j := by
    intro j z hz
    apply ContinuousLinearMap.opNorm_le_bound _ (ubd_nonneg ν s x M j)
    intro v
    rw [fderiv_term]
    exact hval j z hz v
  have hf0 : Summable (fun n : ℤ => psiPhi ν s M (xj ν n x)) := by
    apply Summable.of_norm_bounded hu
    intro j
    rw [Real.norm_eq_abs]
    have h1 := psiPhi_abs_le ν s ha1 M (xj ν j x)
    have h2 := ball_geom ν s ha1 x x (by simp) j
    have hK := Kmat_nonneg M
    have hpos : 0 ≤ 64 * (1 + |x.2|) ^ 3 * Real.exp (1 / (4 * ageA ν s)) *
        ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
          Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
      positivity
    have h5 : 2 * Kmat M * ((1 + ‖xj ν j x‖) ^ 3 *
        Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) ≤ ubd ν s x M j := by
      unfold ubd
      have h6 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 2 * Kmat M)
      nlinarith [mul_nonneg hK hpos, h6]
    exact h1.trans h5
  have hF : ∀ (n : ℤ) (z : ℝ × ℝ), z ∈ Metric.ball x 1 →
      HasFDerivAt (fun w => psiPhi ν s M (xj ν n w))
        (fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) z) z :=
    fun n z _ => (term_diff ν s M n z).hasFDerivAt
  have hbound : ∀ (n : ℤ) (z : ℝ × ℝ), z ∈ Metric.ball x 1 →
      ‖fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) z‖ ≤ ubd ν s x M n :=
    fun n z hz => hfb n z (mem_ball_iff_norm.mp hz)
  refine ⟨hasFDerivAt_tsum_of_isPreconnected
    (f := fun n (w : ℝ × ℝ) => psiPhi ν s M (xj ν n w))
    (f' := fun n z => fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) z)
    (u := ubd ν s x M) hu Metric.isOpen_ball (convex_ball x 1).isPreconnected hF hbound
    (Metric.mem_ball_self one_pos) hf0 (Metric.mem_ball_self one_pos), ?_⟩
  exact Summable.of_norm_bounded hu (fun n => hbound n x (Metric.mem_ball_self one_pos))

theorem ei_one : ei 1 = ((0 : ℝ), (1 : ℝ)) := by simp [ei]

theorem fderiv_psipA_ei (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (hν : 0 < ν) (hs : 0 < s)
    (y : ℝ × ℝ) :
    fderiv ℝ (psipA ν χ A s) y (ei 1) =
      ∑' n : ℤ, psiPhiD ν s (Ay ν χ A s) (xj ν n y) (0, 1) := by
  have ha : 0 < ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hF : psipA ν χ A s = fun z => ∑' n : ℤ, psiPhi ν s (Ay ν χ A s) (xj ν n z) :=
    funext fun z => psipA_eq_phi ν χ A s z ha
  obtain ⟨h, hsum⟩ := psiPhi_tsum_hasFDerivAt ν s hν hs (Ay ν χ A s) y
  rw [hF, h.fderiv, ei_one]
  have := (hsum.hasSum.mapL (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ)))).tsum_eq
  simp only [ContinuousLinearMap.apply_apply] at this
  rw [← this]
  exact tsum_congr fun n => fderiv_term ν s (Ay ν χ A s) n y _

/-! ## Second derivative of the lattice terms -/

theorem G_diff (ν s : ℝ) (M : Mat3) (j : ℤ) (z : ℝ × ℝ) :
    DifferentiableAt ℝ (fun w => psiPhiD ν s M (xj ν j w) (0, 1)) z := by
  unfold psiPhiD xj sq2 merApply merTrace
  fun_prop

theorem fderiv_G (ν s : ℝ) (M : Mat3) (j : ℤ) (z w : ℝ × ℝ) :
    fderiv ℝ (fun u => psiPhiD ν s M (xj ν j u) (0, 1)) z w = pxD ν s M (xj ν j z) w := by
  rw [gp_fderiv_line _ z w (G_diff ν s M j z)]
  have e : ∀ t : ℝ, xj ν j (z + t • w) = xj ν j z + t • w := fun t => by
    ext <;> simp [xj] <;> ring
  have hl : HasDerivAt (fun t : ℝ => psiPhiD ν s M (xj ν j (z + t • w)) (0, 1))
      (pxD ν s M (xj ν j z) w) 0 := by
    simp only [e]
    exact px_line ν s M (xj ν j z) w
  exact hl.deriv

def ub4 (ν s : ℝ) (x : ℝ × ℝ) (K : ℝ) (j : ℤ) : ℝ :=
  10 * K * (256 * (1 + |x.2|) ^ 4 * Real.exp (1 / (4 * ageA ν s))) *
    ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 4 *
      Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2))

theorem fderiv_G_bound (ν s : ℝ) (ha1 : 1 ≤ ageA ν s) (M : Mat3) (x z : ℝ × ℝ)
    (hz : ‖z - x‖ < 1) (j : ℤ) :
    ‖fderiv ℝ (fun u => psiPhiD ν s M (xj ν j u) (0, 1)) z‖ ≤ ub4 ν s x ‖M‖ j := by
  have hK : 0 ≤ ‖M‖ := norm_nonneg M
  have hub : 0 ≤ ub4 ν s x ‖M‖ j := by unfold ub4; positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hub
  intro w
  rw [fderiv_G, Real.norm_eq_abs]
  have hR := norm_nonneg (xj ν j z)
  have hn := norm_nonneg w
  have h1 : |pxD ν s M (xj ν j z) w| ≤ Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) *
      (10 * ‖M‖ * ‖w‖ * (1 + ‖xj ν j z‖) ^ 4) :=
    px_real_bound (ageA ν s) _ ‖M‖ ‖xj ν j z‖ ‖w‖ _ _ _ _ (M 0 0) (M 0 2) (M 2 0) (M 2 2) ha1
      (Real.exp_pos _).le hR hn (abs_fst_le' _) (abs_snd_le' _) (abs_fst_le' _) (abs_snd_le' _)
      (sp_entry_le M 0 0) (sp_entry_le M 0 2) (sp_entry_le M 2 0) (sp_entry_le M 2 2)
  have h2 := ball_geom4 ν s ha1 x z hz j
  refine h1.trans ?_
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 10 * ‖M‖ * ‖w‖)
  unfold ub4
  nlinarith [h3]

theorem ub4_summable (ν s : ℝ) (ha1 : 1 ≤ ageA ν s) (x : ℝ × ℝ) (K : ℝ) (hν : 0 < ν) :
    Summable (ub4 ν s x K) := by
  have ha0 : 0 < ageA ν s := by linarith
  have hα0 : 0 < 1 / (8 * ageA ν s) := by positivity
  have hc : 0 < cOf ν := by unfold cOf; positivity
  exact (sp_poly4_summable x.1 (1 / (8 * ageA ν s)) (cOf ν) hα0 hc).mul_left
    (10 * K * (256 * (1 + |x.2|) ^ 4 * Real.exp (1 / (4 * ageA ν s))))

/-! ## The target -/

theorem psipAXSecond (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) : PsipAXSecond as χf := by
  unfold PsipAXSecond
  intro ν hν A hA s hs x
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have heq : (fun y => fderiv ℝ (psipA ν χf A s) y (ei 1)) =
      fun y => ∑' n : ℤ, psiPhiD ν s (Ay ν χf A s) (xj ν n y) (0, 1) :=
    funext fun y => fderiv_psipA_ei ν χf A s hν hs y
  rw [heq]
  have hu := ub4_summable ν s ha1 x ‖Ay ν χf A s‖ hν
  obtain ⟨-, hsum⟩ := psiPhi_tsum_hasFDerivAt ν s hν hs (Ay ν χf A s) x
  have hf0 : Summable (fun n : ℤ => psiPhiD ν s (Ay ν χf A s) (xj ν n x) (0, 1)) := by
    have := hsum.mapL (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ)))
    simp only [ContinuousLinearMap.apply_apply] at this
    exact this.congr fun n => fderiv_term ν s (Ay ν χf A s) n x _
  have key := hasFDerivAt_tsum_of_isPreconnected
    (f := fun n (w : ℝ × ℝ) => psiPhiD ν s (Ay ν χf A s) (xj ν n w) (0, 1))
    (f' := fun n z => fderiv ℝ (fun u => psiPhiD ν s (Ay ν χf A s) (xj ν n u) (0, 1)) z)
    (u := ub4 ν s x ‖Ay ν χf A s‖) hu Metric.isOpen_ball (convex_ball x 1).isPreconnected
    (fun n z _ => (G_diff ν s (Ay ν χf A s) n z).hasFDerivAt)
    (fun n z hz => fderiv_G_bound ν s ha1 (Ay ν χf A s) x z (mem_ball_iff_norm.mp hz) n)
    (Metric.mem_ball_self one_pos) hf0 (Metric.mem_ball_self one_pos)
  exact key.differentiableAt

end UnforcedLeray.Short.PartIIIb.Concrete
