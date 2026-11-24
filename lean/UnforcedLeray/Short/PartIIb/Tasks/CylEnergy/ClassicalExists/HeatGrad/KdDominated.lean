import UnforcedLeray.Short.PartIIb.Sub.T22_1_6

/-!
# `PartII-b:T22/1/6/1`: the local integrable majorant of `|∂_i K_a(x - y)|`

Proves `HeatKdDominated` (leaf K1 of `T22/1/6`, source `the November 2 reference manuscript`
lines 2103-2105). For `a > 0`, `i`, `x₀` the majorant is
`G(y) = C · exp(-b (x₀₁ - y₁)²) exp(-b (x₀₂ - y₂)²)` with `b = 1/(16a)`, which is integrable as a
product of one-dimensional Gaussians.

Mechanism: with `z = x - y`, `w = x₀ - y`, `|z_j - w_j| < 1`, one has `z_j² ≥ w_j²/2 - 1`, so
`K_a(z) ≤ (4πa)⁻¹ e^{1/(2a)} t²` where `t = e^{-b w₁²} e^{-b w₂²}`; and `(|w_i| + 1) t ≤ 2 + 16a`
because `|w_i| + 1 ≤ (2 + 16a)(1 + s)` with `s = b(w₁² + w₂²)` and `(1 + s) e^{-s} ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace UnforcedLeray.Short.IIb.CylPDE

namespace KdDom

/-- The one-dimensional factor `e^{-b u²}` with `b = 1/(16a)`. -/
def gw (a u : ℝ) : ℝ := Real.exp (-(1 / (16 * a)) * u ^ 2)

lemma gw_nonneg (a u : ℝ) : 0 ≤ gw a u := (Real.exp_pos _).le

lemma heatK_pos {a : ℝ} (ha : 0 < a) (z : Pl) : 0 < heatK a z := by
  unfold heatK
  have h4 : 0 < 4 * Real.pi * a := by have := Real.pi_pos; positivity
  have : 0 < 1 / (4 * Real.pi * a) := by positivity
  exact mul_pos this (Real.exp_pos _)

/-- `(1 + |u|) e^{-b u²} e^{-b v²} ≤ 2 + 16a`. -/
lemma cap_aux {a : ℝ} (ha : 0 < a) (u v : ℝ) :
    (|u| + 1) * (gw a u * gw a v) ≤ 2 + 16 * a := by
  unfold gw
  have hb : 0 < 1 / (16 * a) := by positivity
  set b : ℝ := 1 / (16 * a) with hb_def
  set s : ℝ := b * u ^ 2 + b * v ^ 2 with hs_def
  have hs0 : 0 ≤ s := by rw [hs_def]; positivity
  have hprod : Real.exp (-b * u ^ 2) * Real.exp (-b * v ^ 2) = Real.exp (-s) := by
    rw [← Real.exp_add, hs_def]
    congr 1
    ring
  have hexp_le : (1 + s) * Real.exp (-s) ≤ 1 := by
    have h1 : 1 + s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
    have h2 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    have h3 : 0 < Real.exp (-s) := Real.exp_pos _
    calc (1 + s) * Real.exp (-s) ≤ Real.exp s * Real.exp (-s) :=
          mul_le_mul_of_nonneg_right h1 h3.le
      _ = 1 := h2
  have hu2 : u ^ 2 ≤ 16 * a * s := by
    have h1 : b * u ^ 2 ≤ s := by rw [hs_def]; nlinarith [mul_nonneg hb.le (sq_nonneg v)]
    have h2 : 16 * a * b = 1 := by rw [hb_def]; field_simp
    have h3 : 16 * a * (b * u ^ 2) = u ^ 2 := by
      rw [show 16 * a * (b * u ^ 2) = (16 * a * b) * u ^ 2 by ring, h2, one_mul]
    have h4 := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 16 * a by linarith)
    linarith
  have hu : |u| + 1 ≤ (2 + 16 * a) * (1 + s) := by
    nlinarith [sq_nonneg (|u| - 1 / 2), sq_abs u, hu2, hs0, ha]
  calc (|u| + 1) * (Real.exp (-b * u ^ 2) * Real.exp (-b * v ^ 2))
      = (|u| + 1) * Real.exp (-s) := by rw [hprod]
    _ ≤ (2 + 16 * a) * (1 + s) * Real.exp (-s) :=
        mul_le_mul_of_nonneg_right hu (Real.exp_pos _).le
    _ = (2 + 16 * a) * ((1 + s) * Real.exp (-s)) := by ring
    _ ≤ (2 + 16 * a) * 1 := mul_le_mul_of_nonneg_left hexp_le (by linarith)
    _ = 2 + 16 * a := mul_one _

/-- Gaussian upper bound for the heat kernel in terms of `w = x₀ - y`. -/
lemma heatK_le {a : ℝ} (ha : 0 < a) (z : Pl) (w1 w2 : ℝ) (h1 : |z.1 - w1| < 1)
    (h2 : |z.2 - w2| < 1) :
    heatK a z ≤ 1 / (4 * Real.pi * a) * Real.exp (1 / (2 * a)) *
      ((gw a w1 * gw a w2) * (gw a w1 * gw a w2)) := by
  unfold heatK
  have hd1 : (z.1 - w1) ^ 2 < 1 := by nlinarith [sq_abs (z.1 - w1), abs_nonneg (z.1 - w1)]
  have hd2 : (z.2 - w2) ^ 2 < 1 := by nlinarith [sq_abs (z.2 - w2), abs_nonneg (z.2 - w2)]
  have hq : (w1 ^ 2 + w2 ^ 2) / 2 - 2 ≤ z.1 ^ 2 + z.2 ^ 2 := by
    nlinarith [sq_nonneg (w1 + 2 * (z.1 - w1)), sq_nonneg (w2 + 2 * (z.2 - w2))]
  have hdiv : -(z.1 ^ 2 + z.2 ^ 2) / (4 * a) ≤ -((w1 ^ 2 + w2 ^ 2) / 2 - 2) / (4 * a) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have e1 : -((w1 ^ 2 + w2 ^ 2) / 2 - 2) / (4 * a)
      = 1 / (2 * a) - 2 * ((1 / (16 * a)) * w1 ^ 2 + (1 / (16 * a)) * w2 ^ 2) := by
    field_simp
    ring
  have hT : (gw a w1 * gw a w2) * (gw a w1 * gw a w2)
      = Real.exp (-(2 * ((1 / (16 * a)) * w1 ^ 2 + (1 / (16 * a)) * w2 ^ 2))) := by
    unfold gw
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hmain : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))
      ≤ Real.exp (1 / (2 * a)) * ((gw a w1 * gw a w2) * (gw a w1 * gw a w2)) := by
    rw [hT]
    calc Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))
        ≤ Real.exp (1 / (2 * a) - 2 * ((1 / (16 * a)) * w1 ^ 2 + (1 / (16 * a)) * w2 ^ 2)) :=
          Real.exp_le_exp.mpr (by rw [← e1]; exact hdiv)
      _ = Real.exp (1 / (2 * a)) * Real.exp (-(2 * ((1 / (16 * a)) * w1 ^ 2 + (1 / (16 * a)) * w2 ^ 2))) := by
          rw [← Real.exp_add]
          congr 1
  calc 1 / (4 * Real.pi * a) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))
      ≤ 1 / (4 * Real.pi * a) * (Real.exp (1 / (2 * a)) * ((gw a w1 * gw a w2) * (gw a w1 * gw a w2))) :=
        mul_le_mul_of_nonneg_left hmain (by have := Real.pi_pos; positivity)
    _ = 1 / (4 * Real.pi * a) * Real.exp (1 / (2 * a)) *
        ((gw a w1 * gw a w2) * (gw a w1 * gw a w2)) := by ring

/-- Pure real estimate for one coordinate. -/
lemma final_real {a C0 t H c wi : ℝ} (ha : 0 < a) (hC0 : 0 ≤ C0) (ht : 0 ≤ t) (hH : 0 ≤ H)
    (hHle : H ≤ C0 * (t * t)) (hc : |c| ≤ |wi| + 1) (hcap : (|wi| + 1) * t ≤ 2 + 16 * a) :
    |c| / (2 * a) * H ≤ 1 / (2 * a) * C0 * (2 + 16 * a) * t := by
  have h2a : 0 < 2 * a := by linarith
  have e1 : |c| / (2 * a) * H ≤ (|wi| + 1) / (2 * a) * (C0 * (t * t)) :=
    mul_le_mul (div_le_div_of_nonneg_right hc h2a.le) hHle hH (by positivity)
  have e2 : (|wi| + 1) / (2 * a) * (C0 * (t * t)) = 1 / (2 * a) * C0 * (((|wi| + 1) * t) * t) := by
    ring
  have e3 : ((|wi| + 1) * t) * t ≤ (2 + 16 * a) * t := mul_le_mul_of_nonneg_right hcap ht
  have e4 : 1 / (2 * a) * C0 * (((|wi| + 1) * t) * t) ≤ 1 / (2 * a) * C0 * ((2 + 16 * a) * t) :=
    mul_le_mul_of_nonneg_left e3 (mul_nonneg (by positivity) hC0)
  calc |c| / (2 * a) * H ≤ (|wi| + 1) / (2 * a) * (C0 * (t * t)) := e1
    _ = 1 / (2 * a) * C0 * (((|wi| + 1) * t) * t) := e2
    _ ≤ 1 / (2 * a) * C0 * ((2 + 16 * a) * t) := e4
    _ = 1 / (2 * a) * C0 * (2 + 16 * a) * t := by ring

lemma heatKd_le {a : ℝ} (ha : 0 < a) (z w : Pl) (h1 : |z.1 - w.1| < 1) (h2 : |z.2 - w.2| < 1)
    (i : Fin 2) :
    |heatKd i a z| ≤ 1 / (2 * a) * (1 / (4 * Real.pi * a) * Real.exp (1 / (2 * a))) *
      (2 + 16 * a) * (gw a w.1 * gw a w.2) := by
  have hH := heatK_le ha z w.1 w.2 h1 h2
  have hpos := heatK_pos ha z
  have ht : 0 ≤ gw a w.1 * gw a w.2 := mul_nonneg (gw_nonneg _ _) (gw_nonneg _ _)
  have hcap1 : (|w.1| + 1) * (gw a w.1 * gw a w.2) ≤ 2 + 16 * a := cap_aux ha w.1 w.2
  have hcap2 : (|w.2| + 1) * (gw a w.1 * gw a w.2) ≤ 2 + 16 * a := by
    have := cap_aux ha w.2 w.1
    rw [mul_comm (gw a w.2)] at this
    exact this
  have hC0 : 0 ≤ 1 / (4 * Real.pi * a) * Real.exp (1 / (2 * a)) := by
    have := Real.pi_pos
    positivity
  have hc1 : |z.1| ≤ |w.1| + 1 := by
    have := abs_sub_abs_le_abs_sub z.1 w.1
    linarith
  have hc2 : |z.2| ≤ |w.2| + 1 := by
    have := abs_sub_abs_le_abs_sub z.2 w.2
    linarith
  fin_cases i
  · show |-z.1 / (2 * a) * heatK a z| ≤ _
    rw [abs_mul, abs_div, abs_neg, abs_of_pos (by linarith : (0:ℝ) < 2 * a), abs_of_pos hpos]
    exact final_real ha hC0 ht hpos.le hH hc1 hcap1
  · show |-z.2 / (2 * a) * heatK a z| ≤ _
    rw [abs_mul, abs_div, abs_neg, abs_of_pos (by linarith : (0:ℝ) < 2 * a), abs_of_pos hpos]
    exact final_real ha hC0 ht hpos.le hH hc2 hcap2

end KdDom

open KdDom

/-- **Leaf K1** (`PartII-b:T22/1/6/1`): the local integrable majorant of `∂_i K_a(x - y)`. -/
theorem heatKdDominated : UnforcedLeray.Short.IIb.CylPDE.HeatKdDominated := by
  intro a ha i x0
  have hb : 0 < 1 / (16 * a) := by positivity
  have hf1 : Integrable (fun t : ℝ => gw a (x0.1 - t)) := by
    unfold gw
    exact (integrable_exp_neg_mul_sq hb).comp_sub_left x0.1
  have hf2 : Integrable (fun t : ℝ => gw a (x0.2 - t)) := by
    unfold gw
    exact (integrable_exp_neg_mul_sq hb).comp_sub_left x0.2
  have hP : Integrable (fun y : Pl => gw a (x0.1 - y.1) * gw a (x0.2 - y.2)) :=
    hf1.mul_prod hf2
  refine ⟨fun y => (1 / (2 * a) * (1 / (4 * Real.pi * a) * Real.exp (1 / (2 * a))) *
      (2 + 16 * a)) * (gw a (x0.1 - y.1) * gw a (x0.2 - y.2)), hP.const_mul _, ?_⟩
  intro x hx y
  have hd : dist x x0 < 1 := mem_ball.mp hx
  rw [Prod.dist_eq] at hd
  have h1 : dist x.1 x0.1 < 1 := lt_of_le_of_lt (le_max_left _ _) hd
  have h2 : dist x.2 x0.2 < 1 := lt_of_le_of_lt (le_max_right _ _) hd
  rw [Real.dist_eq] at h1 h2
  have e1 : (x - y).1 - (x0 - y).1 = x.1 - x0.1 := by simp only [Prod.fst_sub]; ring
  have e2 : (x - y).2 - (x0 - y).2 = x.2 - x0.2 := by simp only [Prod.snd_sub]; ring
  have hb1 : |(x - y).1 - (x0 - y).1| < 1 := by rw [e1]; exact h1
  have hb2 : |(x - y).2 - (x0 - y).2| < 1 := by rw [e2]; exact h2
  have key := heatKd_le ha (x - y) (x0 - y) hb1 hb2 i
  simp only [Prod.fst_sub, Prod.snd_sub] at key
  calc |heatKd i a (x - y)| ≤ _ := key
    _ = _ := by ring

end UnforcedLeray.Short.IIb.CylPDE
