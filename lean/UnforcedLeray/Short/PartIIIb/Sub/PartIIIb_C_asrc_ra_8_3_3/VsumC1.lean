import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# `PartIII-b:C/asrc/ra/8/3/3` leaf `VsumC1`: `Σ_j V_j` is `C¹` for `ν, s > 0`

Source 4963, 4978. For fixed `ν, s` the sum `vsum ν s = Σ_k V_k` is differentiated termwise on
unit balls: each term and its derivative are bounded on `ball x0 1` by a fixed Gaussian lattice
majorant `K (1+|x0.1 - kc|)³ exp(-(x0.1 - kc)²/(8a))`, which is summable in `k`
(`gp_poly_summable`). The `C¹` property then follows from `hasFDerivAt_tsum_of_isPreconnected`,
`continuousOn_tsum` and `contDiff_one_iff_fderiv`.
-/

set_option autoImplicit false

noncomputable section

open Set Real Metric

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Shift comparison: if `|d - y| ≤ 1` then `1 + |y| ≤ 2(1 + |d|)` and the Gaussian weight at `y`
is dominated by the one at `d`. -/
lemma vsumC1_shift (a d y : ℝ) (ha : 0 < a) (h : |d - y| ≤ 1) :
    1 + |y| ≤ 2 * (1 + |d|) ∧
      Real.exp (-(1 / (4 * a)) * y ^ 2) ≤
        Real.exp (1 / (4 * a)) * Real.exp (-(1 / (8 * a)) * d ^ 2) := by
  have h1 : |y| ≤ |d| + 1 := by
    have h2 := abs_sub d (d - y)
    rw [show d - (d - y) = y by ring] at h2
    linarith
  refine ⟨by linarith [abs_nonneg d], ?_⟩
  have hsq : (d - y) ^ 2 ≤ 1 := by
    nlinarith [sq_abs (d - y), abs_nonneg (d - y)]
  have hd : d ^ 2 ≤ 2 * y ^ 2 + 2 := by nlinarith [sq_nonneg (d - 2 * y)]
  have ht : (0:ℝ) ≤ 1 / (4 * a) := by positivity
  have h8 : 1 / (8 * a) = (1 / (4 * a)) / 2 := by ring
  rw [h8, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hd ht]

/-- The constant of the local Gaussian majorant. -/
def vsumC1_K (a R : ℝ) : ℝ :=
  4 * Real.exp (1 / (4 * a)) * ((a ^ 2)⁻¹ * (1 + a⁻¹) * (1 + R) ^ 2)

/-- Real-number core of the pointwise majorant. -/
lemma vsumC1_real (a k e E G n P D Rp : ℝ) (ha : 0 < a) (hk0 : 0 ≤ k) (he : 0 ≤ e)
    (hE0 : 0 ≤ E) (hEQ : E ≤ e * G) (hG : 0 ≤ G) (hn0 : 0 ≤ n) (hRp : 0 ≤ Rp) (hD : 1 ≤ D)
    (hP1 : 1 ≤ P) (hnP : n ≤ P) (hPD : P ≤ 2 * Rp * D) :
    k * E * n ≤ 4 * e * (k * (1 + a⁻¹) * Rp ^ 2) * D ^ 3 * G ∧
      k * E * (1 + n ^ 2 / a) ≤ 4 * e * (k * (1 + a⁻¹) * Rp ^ 2) * D ^ 3 * G := by
  have hP0 : 0 ≤ P := by linarith
  have hkE : 0 ≤ k * E := mul_nonneg hk0 hE0
  have hinv : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  have hP2 : P ≤ P ^ 2 := by nlinarith
  have hpsq : P ^ 2 ≤ (2 * Rp * D) ^ 2 := pow_le_pow_left₀ hP0 hPD 2
  have hD2 : D ^ 2 ≤ D ^ 3 := by nlinarith
  have hpoly : P ^ 2 ≤ 4 * Rp ^ 2 * D ^ 3 := by
    have e1 : (2 * Rp * D) ^ 2 = 4 * Rp ^ 2 * D ^ 2 := by ring
    have e2 : 4 * Rp ^ 2 * D ^ 2 ≤ 4 * Rp ^ 2 * D ^ 3 :=
      mul_le_mul_of_nonneg_left hD2 (by positivity)
    linarith
  have hgeo : 0 ≤ k * (e * G) := mul_nonneg hk0 (mul_nonneg he hG)
  have hfac : 4 * e * (k * (1 + a⁻¹) * Rp ^ 2) * D ^ 3 * G
      = (k * (e * G) * (4 * Rp ^ 2 * D ^ 3)) * (1 + a⁻¹) := by ring
  have hone : 1 ≤ 1 + a⁻¹ := by linarith
  have hbig : 0 ≤ k * (e * G) * (4 * Rp ^ 2 * D ^ 3) := by
    apply mul_nonneg hgeo
    have : (0:ℝ) ≤ Rp ^ 2 := sq_nonneg Rp
    have : (0:ℝ) ≤ D ^ 3 := by
      have : (0:ℝ) ≤ D := by linarith
      positivity
    positivity
  constructor
  · calc k * E * n ≤ k * E * P := mul_le_mul_of_nonneg_left hnP hkE
      _ ≤ k * E * P ^ 2 := mul_le_mul_of_nonneg_left hP2 hkE
      _ ≤ k * (e * G) * P ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEQ hk0) (sq_nonneg P)
      _ ≤ k * (e * G) * (4 * Rp ^ 2 * D ^ 3) :=
          mul_le_mul_of_nonneg_left hpoly hgeo
      _ ≤ (k * (e * G) * (4 * Rp ^ 2 * D ^ 3)) * (1 + a⁻¹) :=
          le_mul_of_one_le_right hbig hone
      _ = 4 * e * (k * (1 + a⁻¹) * Rp ^ 2) * D ^ 3 * G := hfac.symm
  · have h1 : 1 ≤ P ^ 2 := by nlinarith
    have h2 : n ^ 2 ≤ P ^ 2 := by nlinarith
    have h3 : n ^ 2 * a⁻¹ ≤ P ^ 2 * a⁻¹ := mul_le_mul_of_nonneg_right h2 hinv
    have hq : 1 + n ^ 2 / a ≤ P ^ 2 * (1 + a⁻¹) := by
      rw [div_eq_mul_inv]
      nlinarith
    calc k * E * (1 + n ^ 2 / a) ≤ k * E * (P ^ 2 * (1 + a⁻¹)) :=
          mul_le_mul_of_nonneg_left hq hkE
      _ ≤ k * (e * G) * (P ^ 2 * (1 + a⁻¹)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEQ hk0)
            (mul_nonneg (sq_nonneg P) (by linarith))
      _ ≤ k * (e * G) * (4 * Rp ^ 2 * D ^ 3) * (1 + a⁻¹) := by
          rw [mul_assoc (k * (e * G))]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpoly (by linarith)) hgeo
      _ = 4 * e * (k * (1 + a⁻¹) * Rp ^ 2) * D ^ 3 * G := by ring

/-- Pointwise local majorant for the value and the derivative of `V_j` on a unit ball. -/
lemma vsumC1_majorant (ν s : ℝ) (ha : 0 < ageA ν s) (x0 x : ℝ × ℝ) (hx : dist x x0 < 1)
    (j : ℤ) :
    ‖Vj ν s j x‖ ≤ vsumC1_K (ageA ν s) (|x0.2| + 1) *
        ((1 + |x0.1 - (j : ℝ) * cOf ν|) ^ 3 *
          Real.exp (-(1 / (8 * ageA ν s)) * (x0.1 - (j : ℝ) * cOf ν) ^ 2)) ∧
    ‖fderiv ℝ (Vj ν s j) x‖ ≤ vsumC1_K (ageA ν s) (|x0.2| + 1) *
        ((1 + |x0.1 - (j : ℝ) * cOf ν|) ^ 3 *
          Real.exp (-(1 / (8 * ageA ν s)) * (x0.1 - (j : ℝ) * cOf ν) ^ 2)) := by
  have hn : ‖x - x0‖ < 1 := by rwa [dist_eq_norm] at hx
  have hx1 : |x.1 - x0.1| < 1 := by
    have h := norm_fst_le (x - x0)
    rw [Prod.fst_sub, Real.norm_eq_abs] at h
    linarith
  have hx2 : |x.2 - x0.2| < 1 := by
    have h := norm_snd_le (x - x0)
    rw [Prod.snd_sub, Real.norm_eq_abs] at h
    linarith
  have hx2' : |x.2| ≤ |x0.2| + 1 := by
    have h := abs_add_le x0.2 (x.2 - x0.2)
    rw [show x0.2 + (x.2 - x0.2) = x.2 by ring] at h
    linarith
  have hdy : |(x0.1 - (j : ℝ) * cOf ν) - (x.1 - (j : ℝ) * cOf ν)| ≤ 1 := by
    rw [show (x0.1 - (j : ℝ) * cOf ν) - (x.1 - (j : ℝ) * cOf ν) = -(x.1 - x0.1) by ring,
      abs_neg]
    exact hx1.le
  obtain ⟨hY, hE⟩ := vsumC1_shift (ageA ν s) (x0.1 - (j : ℝ) * cOf ν)
    (x.1 - (j : ℝ) * cOf ν) ha hdy
  have hEx := gp_exp_le ν s ha j x
  have hOne := gp_one_add_norm ν j x
  have hyabs : (0:ℝ) ≤ |x.1 - (j : ℝ) * cOf ν| := abs_nonneg _
  have hRp : 0 ≤ 1 + (|x0.2| + 1) := by positivity
  have hR : 1 + |x.2| ≤ 1 + (|x0.2| + 1) := by linarith
  have hP : 1 + ‖xj ν j x‖ ≤ (1 + (|x0.2| + 1)) * (1 + |x.1 - (j : ℝ) * cOf ν|) :=
    hOne.trans (mul_le_mul_of_nonneg_right hR (by linarith))
  have hE' : Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
      ≤ Real.exp (1 / (4 * ageA ν s)) * Real.exp (-(1 / (8 * ageA ν s)) * (x0.1 - (j : ℝ) * cOf ν) ^ 2) :=
    hEx.trans hE
  have hPD : (1 + (|x0.2| + 1)) * (1 + |x.1 - (j : ℝ) * cOf ν|)
      ≤ 2 * (1 + (|x0.2| + 1)) * (1 + |x0.1 - (j : ℝ) * cOf ν|) := by
    have := mul_le_mul_of_nonneg_left hY hRp
    linarith
  have hP1 : 1 ≤ (1 + (|x0.2| + 1)) * (1 + |x.1 - (j : ℝ) * cOf ν|) := by
    nlinarith [mul_nonneg hRp hyabs, abs_nonneg x0.2]
  have hκ : (0:ℝ) ≤ (ageA ν s ^ 2)⁻¹ := by positivity
  have hEnn : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hG : 0 ≤ Real.exp (-(1 / (8 * ageA ν s)) * (x0.1 - (j : ℝ) * cOf ν) ^ 2) :=
    (Real.exp_pos _).le
  have hD : 1 ≤ 1 + |x0.1 - (j : ℝ) * cOf ν| := by linarith [abs_nonneg (x0.1 - (j : ℝ) * cOf ν)]
  have hcore := vsumC1_real (ageA ν s) ((ageA ν s ^ 2)⁻¹)
    (Real.exp (1 / (4 * ageA ν s)))
    (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))
    (Real.exp (-(1 / (8 * ageA ν s)) * (x0.1 - (j : ℝ) * cOf ν) ^ 2))
    ‖xj ν j x‖
    ((1 + (|x0.2| + 1)) * (1 + |x.1 - (j : ℝ) * cOf ν|))
    (1 + |x0.1 - (j : ℝ) * cOf ν|) (1 + (|x0.2| + 1))
    ha hκ (Real.exp_pos _).le hEnn hE' hG (norm_nonneg _) hRp hD hP1
    (by linarith) hPD
  constructor
  · rw [gp_Vj_norm_eq ν s j x]
    refine hcore.1.trans (le_of_eq ?_)
    unfold vsumC1_K
    ring
  · have hM0 : 0 ≤ (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) := by
      have : 0 ≤ ‖xj ν j x‖ ^ 2 / ageA ν s := div_nonneg (sq_nonneg _) ha.le
      have := mul_nonneg hκ hEnn
      nlinarith
    have hop : ‖fderiv ℝ (Vj ν s j) x‖ ≤
        (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
          (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) :=
      ContinuousLinearMap.opNorm_le_bound _ hM0
        (fun v => gp_fderiv_Vj_norm ν s ha j x v)
    refine hop.trans (hcore.2.trans (le_of_eq ?_))
    unfold vsumC1_K
    ring

/-- `V_j` is `C¹` in the spatial variable. -/
lemma vsumC1_Vj_contDiff (ν s : ℝ) (j : ℤ) : ContDiff ℝ 1 (Vj ν s j) := by
  unfold Vj xj Jrot sq2
  fun_prop

end UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.Concrete in
/-- **Leaf `VsumC1`: `Σ_j V_j` is `C¹` for `ν, s > 0`** (source 4963, 4978). -/
theorem vsumC1 : UnforcedLeray.Short.PartIIIb.Concrete.VsumC1 := by
  intro ν s hν hs
  have ha : 0 < ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hc : 0 < cOf ν := by unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  have hβ : 0 < 1 / (8 * ageA ν s) := by positivity
  have hsum : ∀ x0 : ℝ × ℝ, Summable (fun j : ℤ => vsumC1_K (ageA ν s) (|x0.2| + 1) *
      ((1 + |x0.1 - (j : ℝ) * cOf ν|) ^ 3 *
        Real.exp (-(1 / (8 * ageA ν s)) * (x0.1 - (j : ℝ) * cOf ν) ^ 2))) :=
    fun x0 => (gp_poly_summable x0.1 (1 / (8 * ageA ν s)) (cOf ν) hβ hc).mul_left _
  have key : ∀ x0 x : ℝ × ℝ, x ∈ Metric.ball x0 1 →
      HasFDerivAt (vsum ν s) (∑' k : ℤ, fderiv ℝ (Vj ν s k) x) x := by
    intro x0 x hx
    exact hasFDerivAt_tsum_of_isPreconnected (f := fun k y => Vj ν s k y)
      (f' := fun k y => fderiv ℝ (Vj ν s k) y) (hsum x0) Metric.isOpen_ball
      (convex_ball x0 1).isPreconnected
      (fun n y _ => (gp_Vj_diff ν s n y).hasFDerivAt)
      (fun n y hy => (vsumC1_majorant ν s ha x0 y (Metric.mem_ball.mp hy) n).2)
      (Metric.mem_ball_self one_pos)
      (Summable.of_norm_bounded (hsum x0)
        (fun n => (vsumC1_majorant ν s ha x0 x0 (by simp) n).1)) hx
  have hdiff : ∀ x0 : ℝ × ℝ, DifferentiableAt ℝ (vsum ν s) x0 := fun x0 =>
    (key x0 x0 (Metric.mem_ball_self one_pos)).differentiableAt
  have hcont_on : ∀ x0 : ℝ × ℝ, ContinuousOn
      (fun x => ∑' k : ℤ, fderiv ℝ (Vj ν s k) x) (Metric.ball x0 1) := by
    intro x0
    exact continuousOn_tsum
      (fun k => ((vsumC1_Vj_contDiff ν s k).continuous_fderiv one_ne_zero).continuousOn)
      (hsum x0)
      (fun n y hy => (vsumC1_majorant ν s ha x0 y (Metric.mem_ball.mp hy) n).2)
  refine contDiff_one_iff_fderiv.2 ⟨fun x0 => hdiff x0, continuous_iff_continuousAt.2 fun x0 => ?_⟩
  have heq : Set.EqOn (fderiv ℝ (vsum ν s))
      (fun x => ∑' k : ℤ, fderiv ℝ (Vj ν s k) x) (Metric.ball x0 1) :=
    fun x hx => (key x0 x hx).fderiv
  exact ((hcont_on x0).congr heq).continuousAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))
