import UnforcedLeray.Short.PartI.Sub.PartI_C10

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.B0123

/-- The scalar `cfac` is bounded for `θ ≥ 1` at the unit turnover `v = θ + 1`. -/
theorem norm_cfac_succ_le (lam κ : ℂ) {θ : ℝ} (hθ : 1 ≤ θ) :
    ‖cfac lam κ θ (θ + 1)‖ ≤ Real.exp |lam.re| * (2 : ℝ) ^ |κ.re| := by
  have hθ0 : 0 < θ := by linarith
  have hv0 : 0 < θ + 1 := by linarith
  have hA : ‖Complex.exp (lam * (θ : ℂ))‖ = Real.exp (lam.re * θ) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have hB : ‖Complex.exp (lam * ((θ + 1 : ℝ) : ℂ))‖ = Real.exp (lam.re * (θ + 1)) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have hC : ‖((θ : ℝ) : ℂ) ^ κ‖ = θ ^ κ.re := Complex.norm_cpow_eq_rpow_re_of_pos hθ0 κ
  have hD : ‖((θ + 1 : ℝ) : ℂ) ^ κ‖ = (θ + 1) ^ κ.re := Complex.norm_cpow_eq_rpow_re_of_pos hv0 κ
  have hnorm : ‖cfac lam κ θ (θ + 1)‖ =
      Real.exp (lam.re * θ) * θ ^ κ.re * (Real.exp (lam.re * (θ + 1)) * (θ + 1) ^ κ.re)⁻¹ := by
    unfold cfac
    rw [norm_mul, norm_mul, norm_inv, norm_mul, hA, hB, hC, hD]
  have e : Real.exp (lam.re * θ) * θ ^ κ.re * (Real.exp (lam.re * (θ + 1)) * (θ + 1) ^ κ.re)⁻¹
      = Real.exp (-lam.re) * (θ ^ κ.re / (θ + 1) ^ κ.re) := by
    have h1 : Real.exp (lam.re * θ) / Real.exp (lam.re * (θ + 1)) = Real.exp (-lam.re) := by
      rw [← Real.exp_sub]; congr 1; ring
    rw [← h1]; ring
  have hx : θ ^ κ.re / (θ + 1) ^ κ.re ≤ (2 : ℝ) ^ |κ.re| := by
    rw [← Real.div_rpow hθ0.le hv0.le]
    have hx0 : 0 ≤ θ / (θ + 1) := by positivity
    have hx1 : θ / (θ + 1) ≤ 1 := by rw [div_le_one hv0]; linarith
    have hx2 : (1 / 2 : ℝ) ≤ θ / (θ + 1) := by rw [le_div_iff₀ hv0]; linarith
    rcases le_total 0 κ.re with hr | hr
    · rw [abs_of_nonneg hr]
      have h1 := Real.rpow_le_one hx0 hx1 hr
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ κ.re := Real.one_le_rpow (by norm_num) hr
      linarith
    · rw [abs_of_nonpos hr]
      have h1 : (θ / (θ + 1)) ^ κ.re ≤ (1 / 2 : ℝ) ^ κ.re :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx2 hr
      have h2 : (1 / 2 : ℝ) ^ κ.re = (2 : ℝ) ^ (-κ.re) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.div_rpow zero_le_one (by norm_num),
          Real.one_rpow, one_div]
      exact h1.trans h2.le
  have hexp : Real.exp (-lam.re) ≤ Real.exp |lam.re| :=
    Real.exp_le_exp.2 (by linarith [neg_le_abs lam.re])
  rw [hnorm, e]
  exact mul_le_mul hexp hx (div_nonneg (Real.rpow_nonneg hθ0.le _) (Real.rpow_nonneg hv0.le _))
    (Real.exp_pos _).le

/-- Scalar multiplication in the graph norm of `X_{G,j}`. -/
theorem graphNormSq_smul_mk (j : ℕ) (c : ℂ) (y : B0010.XG) (hy : y ∈ (B0121.fracPow j).domain)
    (hcy : c • y ∈ (B0121.fracPow j).domain) :
    B0121.graphNormSq j ⟨c • y, hcy⟩ = ‖c‖ ^ 2 * B0121.graphNormSq j ⟨y, hy⟩ := by
  have e : (⟨c • y, hcy⟩ : (B0121.fracPow j).domain) = c • (⟨y, hy⟩ : (B0121.fracPow j).domain) :=
    rfl
  rw [e]
  unfold B0121.graphNormSq
  rw [LinearPMap.map_smul]
  simp only [Submodule.coe_smul, norm_smul, mul_pow]
  ring

/-- **Free term gain** (source 1139-1145). -/
theorem freeTermGain (lam κ : ℂ) (j : ℕ) : FreeTermGain lam κ j := by
  refine ⟨Real.exp |lam.re| * (2 : ℝ) ^ |κ.re| + 1, by positivity, ?_⟩
  intro θ hθ x
  have hθ0 : 0 < θ := by linarith
  have hv0 : 0 < θ + 1 := by linarith
  have ha0 : 0 < Real.log (θ + 1) - Real.log θ := by
    have := Real.log_lt_log hθ0 (show θ < θ + 1 by linarith)
    linarith
  have ha1 : Real.log (θ + 1) - Real.log θ ≤ 1 := by
    rw [← Real.log_div hv0.ne' hθ0.ne']
    have h1 := Real.log_le_sub_one_of_pos (show 0 < (θ + 1) / θ by positivity)
    have h2 : (θ + 1) / θ ≤ 2 := by rw [div_le_iff₀ hθ0]; linarith
    linarith
  have hinv : (Real.log (θ + 1) - Real.log θ)⁻¹ ≤ 1 + θ := by
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < (θ + 1) / θ by positivity)
    rw [Real.log_div hv0.ne' hθ0.ne'] at h1
    have e : 1 - ((θ + 1) / θ)⁻¹ = 1 / (θ + 1) := by
      field_simp
      ring
    rw [e] at h1
    have h3 : 1 ≤ (Real.log (θ + 1) - Real.log θ) * (θ + 1) := (div_le_iff₀ hv0).1 h1
    have h4 : (Real.log (θ + 1) - Real.log θ)⁻¹ * ((Real.log (θ + 1) - Real.log θ) * (θ + 1))
        = θ + 1 := by
      rw [← mul_assoc, inv_mul_cancel₀ ha0.ne', one_mul]
    have h5 := le_mul_of_one_le_right (inv_nonneg.2 ha0.le) h3
    linarith
  have hcC : ∀ θ' : ℝ, 1 ≤ θ' → ‖cfac lam κ θ' (θ' + 1)‖ ≤
      Real.exp |lam.re| * (2 : ℝ) ^ |κ.re| + 1 := fun θ' hθ' => by
    linarith [norm_cfac_succ_le lam κ hθ']
  obtain ⟨h0, hbd⟩ := eq_st18_t00101_graphNormSq j ha0 ha1 x
  refine ⟨Submodule.smul_mem _ _ h0, ?_⟩
  rw [graphNormSq_smul_mk (j + 1) _ _ h0]
  have hG0 : 0 ≤ B0121.graphNormSq j x := by unfold B0121.graphNormSq; positivity
  have hG1 : 0 ≤ B0121.graphNormSq (j + 1) ⟨expD (Real.log (θ + 1) - Real.log θ) (x : B0010.XG), h0⟩ := by
    unfold B0121.graphNormSq; positivity
  have hc2 := pow_le_pow_left₀ (norm_nonneg _) (hcC θ hθ) 2
  have hs : ((1 + θ) ^ (1 / 2 : ℝ)) ^ 2 = 1 + θ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have key := hbd.trans (mul_le_mul_of_nonneg_right hinv hG0)
  calc _ ≤ (Real.exp |lam.re| * (2 : ℝ) ^ |κ.re| + 1) ^ 2 *
          ((1 + θ) * B0121.graphNormSq j x) := mul_le_mul hc2 key hG1 (sq_nonneg _)
    _ = _ := by rw [mul_pow, hs]; ring

end UnforcedLeray.Short.PartI
