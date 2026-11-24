import UnforcedLeray.Short.PartI.Sub.PartI_C10

/-!
# `PartI:C10/2`: the `j = 0` bound for `W = e^{λθ}θ^κ V`

At `j = 0` the weight `(1+ℓ)^{0}` is `1`, so `X_{G,0}` is all of `X_G` and the graph norm is
`2‖f‖²`.  The canonical asymptotic `‖W(θ) - q‖ ≤ C/θ` then gives `‖W(θ)‖ ≤ ‖q‖ + |C|/b` for `θ ≥ b`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.B0123

/-- At level `0` the squared graph norm is twice the squared norm. -/
theorem graphNormSq_zero (f : (B0121.fracPow 0).domain) :
    B0121.graphNormSq 0 f = 2 * ‖(f : B0010.XG)‖ ^ 2 := by
  rw [B0121.graphNormSq_eq, B0121.norm_sq_eq_tsum, ← tsum_mul_left]
  congr 1
  funext ℓ
  norm_num

theorem wGraphBound_zero {lam κ : ℂ} {q : B0010.XG} {V : ℝ → B0010.XG} (hA : HasCanonicalAsymptotic lam κ q V) : WGraphBound (fun θ : ℝ => Complex.exp (lam * θ) • (θ : ℂ) ^ κ • V θ) 0 := by
  obtain ⟨C, b, hb, hW⟩ := hA
  refine ⟨2 * (‖q‖ + |C| / b), b, hb, fun θ hθ => ?_⟩
  dsimp only
  have hθ0 : 0 < θ := lt_of_lt_of_le hb hθ
  have hmem : Complex.exp (lam * θ) • (θ : ℂ) ^ κ • V θ ∈ (B0121.fracPow 0).domain := by
    rw [B0121.fracPow_domain, B0121.mem_XGj_iff]
    simp only [pow_zero, one_mul]
    exact B0121.summable_coef_sq _
  refine ⟨hmem, ?_⟩
  rw [graphNormSq_zero]
  have h1 := hW θ hθ
  have h2 := norm_sub_norm_le (Complex.exp (lam * θ) • (θ : ℂ) ^ κ • V θ) q
  have h3 : C / θ ≤ |C| / b := by
    calc C / θ ≤ |C| / θ := by
          gcongr
          exact le_abs_self C
      _ ≤ |C| / b := by gcongr
  have hx : ‖Complex.exp (lam * θ) • (θ : ℂ) ^ κ • V θ‖ ≤ ‖q‖ + |C| / b := by linarith
  have hK : 0 ≤ ‖q‖ + |C| / b := by positivity
  have hnx := norm_nonneg (Complex.exp (lam * θ) • (θ : ℂ) ^ κ • V θ)
  simp only [Subtype.coe_mk, Nat.cast_zero, zero_div, Real.rpow_zero, mul_one]
  nlinarith [mul_le_mul hx hx hnx hK, mul_nonneg hK hK]

end UnforcedLeray.Short.PartI
