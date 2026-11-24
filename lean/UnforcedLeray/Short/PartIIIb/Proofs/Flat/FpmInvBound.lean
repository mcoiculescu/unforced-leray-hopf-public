import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flat_1

/-!
# Proof of `fpmInvBound` (source: `the November 2 reference manuscript`,
lines 4645-4648, 4666-4667)

`|F_+(t,0)⁻¹| = e^{-γ z} x^{-Re κ}` with `x = 1+νt ∈ [1, 2.1]` and `z = t/x ≥ t/3`
on the support. Since `x ≥ 1`, `x^{-Re κ} ≤ 3^{|Re κ|}` for `x ≤ 3`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.ConcreteYF

/-- `F_+(t,0)⁻¹ = e^{-λ z} x^{-κ}` with `x = 1+νt`, `z = t/x` (source 4648). -/
lemma fpm_inv_eq_aux_b (lam κ : ℂ) (ν t : ℝ) :
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

theorem fpmInvBound (lam κ : ℂ) (hlam : 0 < lam.re) : FlatAmp.FpmInvBound lam κ := by
  unfold FlatAmp.FpmInvBound
  refine ⟨(3 : ℝ) ^ |κ.re|, ?_⟩
  intro ν hν t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hνt : ν * t ≤ 1.1 := by
    have := (le_div_iff₀ hν).1 ht1
    linarith [mul_comm t ν]
  have hνt0 : 0 ≤ ν * t := mul_nonneg hν.le ht0
  have hx1 : (1 : ℝ) ≤ 1 + ν * t := by linarith
  have hx0 : (0 : ℝ) < 1 + ν * t := by linarith
  have hx3 : 1 + ν * t ≤ 3 := by norm_num at hνt ⊢; linarith
  have hlam0 : 0 ≤ lam.re := hlam.le
  rw [fpm_inv_eq_aux_b, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.neg_re]
  set z : ℝ := t / (1 + ν * t) with hzdef
  have hz3 : t / 3 ≤ z := by
    rw [hzdef]
    gcongr
  have hE : Real.exp (-lam.re * z) ≤ Real.exp (-(lam.re / 3) * t) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hz3 hlam0
    nlinarith [this]
  have hn1 : ‖Complex.exp (-lam * (z : ℂ))‖ = Real.exp (-lam.re * z) := by
    have hre : (-lam * (z : ℂ)).re = -lam.re * z := by simp
    rw [Complex.norm_exp, hre]
  have h1 : (1 + ν * t) ^ (-κ.re) ≤ (3 : ℝ) ^ |κ.re| := by
    calc (1 + ν * t) ^ (-κ.re) ≤ (1 + ν * t) ^ |κ.re| :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [neg_le_abs κ.re])
      _ ≤ (3 : ℝ) ^ |κ.re| := Real.rpow_le_rpow hx0.le hx3 (abs_nonneg _)
  rw [hn1]
  have hm := mul_le_mul hE h1 (Real.rpow_nonneg hx0.le _) (Real.exp_pos _).le
  calc Real.exp (-lam.re * z) * (1 + ν * t) ^ (-κ.re)
      ≤ Real.exp (-(lam.re / 3) * t) * (3 : ℝ) ^ |κ.re| := hm
    _ = (3 : ℝ) ^ |κ.re| * Real.exp (-(lam.re / 3) * t) := mul_comm _ _

end UnforcedLeray.Short.PartIIIb.ConcreteYF
