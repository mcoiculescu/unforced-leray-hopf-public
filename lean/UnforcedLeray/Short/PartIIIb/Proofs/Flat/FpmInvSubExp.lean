import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flat_1
import UnforcedLeray.Short.PartIIIb.Proofs.Flat.CpowNegSubOne
import UnforcedLeray.Short.PartIIIb.Proofs.Flat.ExpSubExp

/-!
# Proof of `fpmInvSubExp` (source: `the November 2 reference manuscript`,
lines 4648, 4655-4658)

For `0 ≤ t ≤ 1.1/ν`, with `x = 1+νt` and `z = t/x`, `F_+(t,0)⁻¹ = e^{-λz} x^{-κ}` (4648).
Split `F⁻¹ - e^{-λt} = e^{-λz}(x^{-κ} - 1) + (e^{-λz} - e^{-λt})`, then use
`‖x^{-κ}-1‖ ≤ ‖κ‖e^{1.1‖κ‖} νt` (`cpowNegSubOne`), `t - z ≤ νt²` and `z ≥ t/3`
(`expSubExpLe`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.ConcreteYF

/-- `F_+(t,0)⁻¹ = e^{-λ z} x^{-κ}` with `x = 1+νt`, `z = t/x` (source 4648). -/
lemma fpm_inv_eq_aux (lam κ : ℂ) (ν t : ℝ) :
    (UnforcedLeray.Short.PartIIIb.Fpm true lam κ ν t 0)⁻¹ =
      Complex.exp (-lam * ((t / (1 + ν * t) : ℝ) : ℂ)) * ((1 + ν * t : ℝ) : ℂ) ^ (-κ) := by
  rw [FlatAmp.Fpm_true]
  have h0z : UnforcedLeray.Short.PartIIIb.zOf ν 0 = 0 := by
    simp [UnforcedLeray.Short.PartIIIb.zOf]
  have h0a : UnforcedLeray.Short.PartIIIb.aOf ν 0 = 1 := by
    simp [UnforcedLeray.Short.PartIIIb.aOf]
  have hz : UnforcedLeray.Short.PartIIIb.zOf ν t = t / (1 + ν * t) := rfl
  have ha : UnforcedLeray.Short.PartIIIb.aOf ν t = 1 + ν * t := rfl
  rw [h0z, h0a, sub_zero, div_one, hz, ha, mul_inv, ← Complex.exp_neg, ← Complex.cpow_neg,
    neg_mul]

/-- Core estimate on `0 ≤ t`, `νt ≤ 1.1`. -/
lemma fpm_inv_sub_core (lam κ : ℂ) (hlam : 0 < lam.re) (ν t : ℝ) (hν : 0 < ν) (ht0 : 0 ≤ t)
    (hνt : ν * t ≤ 1.1) :
    ‖Complex.exp (-lam * ((t / (1 + ν * t) : ℝ) : ℂ)) * ((1 + ν * t : ℝ) : ℂ) ^ (-κ)
        - Complex.exp (-lam * (t : ℂ))‖ ≤
      (‖κ‖ * Real.exp (1.1 * ‖κ‖) + ‖lam‖) * ν * (t + t ^ 2) * Real.exp (-(lam.re / 3) * t) := by
  have hνt0 : 0 ≤ ν * t := mul_nonneg hν.le ht0
  have hx1 : (1 : ℝ) ≤ 1 + ν * t := by linarith
  have hx0 : (0 : ℝ) < 1 + ν * t := by linarith
  have hx2 : 1 + ν * t ≤ 2.1 := by norm_num at hνt ⊢; linarith
  have hx3 : 1 + ν * t ≤ 3 := by norm_num at hνt ⊢; linarith
  set z : ℝ := t / (1 + ν * t) with hzdef
  have hzt : z ≤ t := div_le_self ht0 hx1
  have hz3 : t / 3 ≤ z := by
    rw [hzdef]
    gcongr
  have hdz : t - z ≤ ν * t ^ 2 := by
    have h3 : 0 ≤ ν ^ 2 * t ^ 3 := by positivity
    have : t - ν * t ^ 2 ≤ z := by
      rw [hzdef, le_div_iff₀ hx0]
      nlinarith [h3]
    linarith
  have hlam0 : 0 ≤ lam.re := hlam.le
  -- norm of the exponential factor
  have hn1 : ‖Complex.exp (-lam * (z : ℂ))‖ = Real.exp (-lam.re * z) := by
    have hre : (-lam * (z : ℂ)).re = -lam.re * z := by simp
    rw [Complex.norm_exp, hre]
  have hE : Real.exp (-lam.re * z) ≤ Real.exp (-(lam.re / 3) * t) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hz3 hlam0
    nlinarith [this]
  have hE1 : 0 ≤ Real.exp (-lam.re * z) := (Real.exp_pos _).le
  -- the cpow factor
  have hc := cpowNegSubOne κ (1 + ν * t) hx1 hx2
  rw [show (1 + ν * t) - 1 = ν * t by ring] at hc
  -- splitting
  have hsplit : Complex.exp (-lam * (z : ℂ)) * ((1 + ν * t : ℝ) : ℂ) ^ (-κ)
      - Complex.exp (-lam * (t : ℂ))
      = Complex.exp (-lam * (z : ℂ)) * (((1 + ν * t : ℝ) : ℂ) ^ (-κ) - 1)
        + (Complex.exp (-lam * (z : ℂ)) - Complex.exp (-lam * (t : ℂ))) := by ring
  rw [hsplit]
  have hT1 : ‖Complex.exp (-lam * (z : ℂ)) * (((1 + ν * t : ℝ) : ℂ) ^ (-κ) - 1)‖
      ≤ Real.exp (-(lam.re / 3) * t) * ((‖κ‖ * Real.exp (1.1 * ‖κ‖)) * (ν * t)) := by
    rw [norm_mul, hn1]
    apply mul_le_mul hE hc (norm_nonneg _) (Real.exp_pos _).le
  have hT2 : ‖Complex.exp (-lam * (z : ℂ)) - Complex.exp (-lam * (t : ℂ))‖
      ≤ ‖lam‖ * (ν * t ^ 2) * Real.exp (-(lam.re / 3) * t) := by
    have h := expSubExpLe lam hlam0 z t hzt
    have hl : 0 ≤ ‖lam‖ := norm_nonneg _
    calc ‖Complex.exp (-lam * (z : ℂ)) - Complex.exp (-lam * (t : ℂ))‖
        ≤ ‖lam‖ * (t - z) * Real.exp (-lam.re * z) := h
      _ ≤ ‖lam‖ * (ν * t ^ 2) * Real.exp (-lam.re * z) := by
          refine mul_le_mul_of_nonneg_right ?_ hE1
          exact mul_le_mul_of_nonneg_left hdz hl
      _ ≤ ‖lam‖ * (ν * t ^ 2) * Real.exp (-(lam.re / 3) * t) := by
          apply mul_le_mul_of_nonneg_left hE
          exact mul_nonneg (norm_nonneg _) (mul_nonneg hν.le (sq_nonneg t))
  have hA : 0 ≤ ‖κ‖ * Real.exp (1.1 * ‖κ‖) := by positivity
  have hP : 0 ≤ Real.exp (-(lam.re / 3) * t) * ((‖κ‖ * Real.exp (1.1 * ‖κ‖)) * (ν * t ^ 2)
      + ‖lam‖ * (ν * t)) :=
    mul_nonneg (Real.exp_pos _).le (add_nonneg
      (mul_nonneg hA (mul_nonneg hν.le (sq_nonneg t)))
      (mul_nonneg (norm_nonneg _) (mul_nonneg hν.le ht0)))
  calc ‖Complex.exp (-lam * (z : ℂ)) * (((1 + ν * t : ℝ) : ℂ) ^ (-κ) - 1)
        + (Complex.exp (-lam * (z : ℂ)) - Complex.exp (-lam * (t : ℂ)))‖
      ≤ ‖Complex.exp (-lam * (z : ℂ)) * (((1 + ν * t : ℝ) : ℂ) ^ (-κ) - 1)‖
          + ‖Complex.exp (-lam * (z : ℂ)) - Complex.exp (-lam * (t : ℂ))‖ := norm_add_le _ _
    _ ≤ Real.exp (-(lam.re / 3) * t) * ((‖κ‖ * Real.exp (1.1 * ‖κ‖)) * (ν * t))
          + ‖lam‖ * (ν * t ^ 2) * Real.exp (-(lam.re / 3) * t) := add_le_add hT1 hT2
    _ ≤ (‖κ‖ * Real.exp (1.1 * ‖κ‖) + ‖lam‖) * ν * (t + t ^ 2) * Real.exp (-(lam.re / 3) * t) := by
          nlinarith [hP]

theorem fpmInvSubExp (lam κ : ℂ) (hlam : 0 < lam.re) : FlatAmp.FpmInvSubExp lam κ := by
  unfold FlatAmp.FpmInvSubExp
  refine ⟨‖κ‖ * Real.exp (1.1 * ‖κ‖) + ‖lam‖, ?_⟩
  intro ν hν t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hνt : ν * t ≤ 1.1 := by
    have := (le_div_iff₀ hν).1 ht1
    linarith [mul_comm t ν]
  rw [fpm_inv_eq_aux]
  exact fpm_inv_sub_core lam κ hlam ν t hν ht0 hνt

end UnforcedLeray.Short.PartIIIb.ConcreteYF
