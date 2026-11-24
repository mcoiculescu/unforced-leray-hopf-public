import UnforcedLeray.Short.PartI.Sub.PartI_C10
import UnforcedLeray.Short.PartI.Tasks.CanonicalGraphNorm.GraphIntegral
import UnforcedLeray.Short.PartI.Tasks.CanonicalGraphNorm.FreeGain
import UnforcedLeray.Short.PartI.Tasks.GreenEllipticRegularity
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# `PartI:C10/5`: the integral term gains one derivative

Source: `the November 2 reference manuscript`, lines 1126-1146.  The Duhamel
integrand is bounded in `X_{G,j+1}` by `C a^{-1/2} ‖L₀ W(v)‖_{X_{G,j}}` with
`a = log v - log θ ≥ (v-θ)/(θ+1)`; Minkowski (`graphIntegralBound`) and `∫_θ^{θ+1}(v-θ)^{-1/2}=2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.B0123

/-- `cfac` is bounded for `θ ≥ 1`, `θ ≤ v ≤ θ + 1`. -/
theorem norm_cfac_le (lam κ : ℂ) {θ v : ℝ} (hθ : 1 ≤ θ) (h2 : θ ≤ v) (h3 : v ≤ θ + 1) :
    ‖cfac lam κ θ v‖ ≤ Real.exp |lam.re| * (2 : ℝ) ^ |κ.re| := by
  have hθ0 : 0 < θ := by linarith
  have hv0 : 0 < v := by linarith
  have hA : ‖Complex.exp (lam * (θ : ℂ))‖ = Real.exp (lam.re * θ) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have hB : ‖Complex.exp (lam * (v : ℂ))‖ = Real.exp (lam.re * v) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have hC : ‖((θ : ℝ) : ℂ) ^ κ‖ = θ ^ κ.re := Complex.norm_cpow_eq_rpow_re_of_pos hθ0 κ
  have hD : ‖((v : ℝ) : ℂ) ^ κ‖ = v ^ κ.re := Complex.norm_cpow_eq_rpow_re_of_pos hv0 κ
  have hnorm : ‖cfac lam κ θ v‖ =
      Real.exp (lam.re * θ) * θ ^ κ.re * (Real.exp (lam.re * v) * v ^ κ.re)⁻¹ := by
    unfold cfac
    rw [norm_mul, norm_mul, norm_inv, norm_mul, hA, hB, hC, hD]
  have e : Real.exp (lam.re * θ) * θ ^ κ.re * (Real.exp (lam.re * v) * v ^ κ.re)⁻¹
      = Real.exp (lam.re * (θ - v)) * (θ ^ κ.re / v ^ κ.re) := by
    have h1 : Real.exp (lam.re * θ) / Real.exp (lam.re * v) = Real.exp (lam.re * (θ - v)) := by
      rw [← Real.exp_sub]; congr 1; ring
    rw [← h1]; ring
  have hx : θ ^ κ.re / v ^ κ.re ≤ (2 : ℝ) ^ |κ.re| := by
    rw [← Real.div_rpow hθ0.le hv0.le]
    have hx0 : 0 ≤ θ / v := by positivity
    have hx1 : θ / v ≤ 1 := by rw [div_le_one hv0]; linarith
    have hx2 : (1 / 2 : ℝ) ≤ θ / v := by rw [le_div_iff₀ hv0]; linarith
    rcases le_total 0 κ.re with hr | hr
    · rw [abs_of_nonneg hr]
      have h1 := Real.rpow_le_one hx0 hx1 hr
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ κ.re := Real.one_le_rpow (by norm_num) hr
      linarith
    · rw [abs_of_nonpos hr]
      have h1 : (θ / v) ^ κ.re ≤ (1 / 2 : ℝ) ^ κ.re :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx2 hr
      have h2 : (1 / 2 : ℝ) ^ κ.re = (2 : ℝ) ^ (-κ.re) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.div_rpow zero_le_one (by norm_num),
          Real.one_rpow, one_div]
      exact h1.trans h2.le
  have hexp : Real.exp (lam.re * (θ - v)) ≤ Real.exp |lam.re| := by
    refine Real.exp_le_exp.2 ?_
    have hab : |θ - v| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc lam.re * (θ - v) ≤ |lam.re * (θ - v)| := le_abs_self _
      _ = |lam.re| * |θ - v| := abs_mul _ _
      _ ≤ |lam.re| * 1 := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
      _ = _ := mul_one _
  rw [hnorm, e]
  exact mul_le_mul hexp hx (div_nonneg (Real.rpow_nonneg hθ0.le _) (Real.rpow_nonneg hv0.le _))
    (Real.exp_pos _).le

/-- `∫_θ^{θ+1} (v-θ)^{-1/2} dv = 2`. -/
theorem integral_rpow_neg_half (θ : ℝ) :
    ∫ v in θ..θ + 1, (v - θ) ^ (-(1 / 2 : ℝ)) = 2 := by
  have h := intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (a := θ)
    (b := θ + 1) θ
  simp only [sub_self, add_sub_cancel_left] at h
  rw [h, integral_rpow (Or.inl (by norm_num))]
  norm_num [Real.zero_rpow, Real.one_rpow]

/-- `a = log v - log θ` satisfies `(v-θ)/(θ+1) ≤ a ≤ 1` for `1 ≤ θ < v ≤ θ + 1`. -/
theorem log_gap_of (θ v : ℝ) (h1 : 1 ≤ θ) (h2 : θ ≤ v) (h3 : v ≤ θ + 1) :
    (v - θ) / (θ + 1) ≤ Real.log v - Real.log θ ∧ Real.log v - Real.log θ ≤ 1 := by
  have hθ0 : 0 < θ := by linarith
  have hv0 : 0 < v := by linarith
  rw [← Real.log_div hv0.ne' hθ0.ne']
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (show 0 < v / θ by positivity)
    have e : 1 - (v / θ)⁻¹ = (v - θ) / v := by field_simp
    rw [e] at h
    refine le_trans ?_ h
    exact div_le_div_of_nonneg_left (by linarith) hv0 h3
  · have h := Real.log_le_sub_one_of_pos (show 0 < v / θ by positivity)
    have : v / θ ≤ 2 := by rw [div_le_iff₀ hθ0]; linarith
    linarith

/-- **Integral term gain** (source 1139-1146). -/
theorem integralTermGain (lam κ : ℂ) (j : ℕ) : IntegralTermGain lam κ j := by
  obtain ⟨C0, hC0, hL⟩ := B0122.L0_mem_XGj_norm j (PartI.greenEllipticRegularity j)
  set cm : ℝ := Real.exp |lam.re| * (2 : ℝ) ^ |κ.re| with hcm
  have hcm0 : 0 ≤ cm := by positivity
  refine ⟨2 * cm * C0 + 1, by positivity, ?_⟩
  intro θ hθ W _ M hM hW
  have hθ0 : 0 < θ := by linarith
  by_cases hint : IntervalIntegrable (fun v => cfac lam κ θ v •
      expD (Real.log v - Real.log θ) (B0012.L0 (W v))) volume θ (θ + 1)
  swap
  · have h0 : (∫ v in θ..θ + 1, cfac lam κ θ v •
        expD (Real.log v - Real.log θ) (B0012.L0 (W v))) = 0 :=
      intervalIntegral.integral_undef hint
    have hm0 : (∫ v in θ..θ + 1, cfac lam κ θ v •
        expD (Real.log v - Real.log θ) (B0012.L0 (W v))) ∈ (B0121.fracPow (j + 1)).domain := by
      rw [h0]; exact Submodule.zero_mem _
    refine ⟨hm0, ?_⟩
    have : (⟨_, hm0⟩ : (B0121.fracPow (j + 1)).domain) = 0 := Subtype.ext h0
    rw [this]
    have : B0121.graphNormSq (j + 1) 0 = 0 := by
      unfold B0121.graphNormSq; simp
    rw [this]; positivity
  set K : ℝ := cm * C0 * M * Real.sqrt (θ + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  set g : ℝ → ℝ := fun v => K * (v - θ) ^ (-(1 / 2 : ℝ)) with hg
  have hgint : IntervalIntegrable g volume θ (θ + 1) := by
    have h1 : IntervalIntegrable (fun v : ℝ => (v - θ) ^ (-(1 / 2 : ℝ))) volume θ (θ + 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := θ - θ) (b := θ + 1 - θ)
        (r := -(1 / 2 : ℝ)) (by norm_num))
      have h2 := IntervalIntegrable.comp_sub_right this θ
      have e1 : θ - θ + θ = θ := by ring
      have e2 : θ + 1 - θ + θ = θ + 1 := by ring
      rw [e1, e2] at h2
      exact h2
    exact h1.const_mul K
  have hbd : ∀ v ∈ Ioc θ (θ + 1), 0 ≤ g v ∧ ∃ h : (cfac lam κ θ v •
      expD (Real.log v - Real.log θ) (B0012.L0 (W v))) ∈ (B0121.fracPow (j + 1)).domain,
        B0121.graphNormSq (j + 1) ⟨_, h⟩ ≤ (g v) ^ 2 := by
    intro v hv
    have hvθ : 0 < v - θ := by linarith [hv.1]
    refine ⟨mul_nonneg hK0 (Real.rpow_nonneg hvθ.le _), ?_⟩
    obtain ⟨hWm, hWb⟩ := hW v ⟨hv.1.le, hv.2⟩
    obtain ⟨hLm, hLb⟩ := hL (W v) hWm
    obtain ⟨ha1, ha2⟩ := log_gap_of θ v hθ hv.1.le hv.2
    have ha0 : 0 < Real.log v - Real.log θ := lt_of_lt_of_le (by positivity) ha1
    obtain ⟨hEm, hEb⟩ := eq_st18_t00101_graphNormSq j ha0 ha2 ⟨B0012.L0 (W v), hLm⟩
    refine ⟨Submodule.smul_mem _ _ hEm, ?_⟩
    rw [graphNormSq_smul_mk (j + 1) _ _ hEm]
    -- bounds
    have hG : B0121.graphNormSq j ⟨B0012.L0 (W v), hLm⟩ ≤ C0 ^ 2 * M ^ 2 := by
      have hn0 : 0 ≤ B0121.graphNormSq j ⟨B0012.L0 (W v), hLm⟩ := by
        unfold B0121.graphNormSq; positivity
      have hn1 : 0 ≤ B0121.graphNormSq j ⟨W v, hWm⟩ := by
        unfold B0121.graphNormSq; positivity
      have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hLb 2
      rw [Real.sq_sqrt hn0, mul_pow, Real.sq_sqrt hn1] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hWb (sq_nonneg _))
    have hinv : (Real.log v - Real.log θ)⁻¹ ≤ (θ + 1) / (v - θ) := by
      rw [← one_div, div_le_div_iff₀ ha0 hvθ]
      have := (div_le_iff₀ (show 0 < θ + 1 by linarith)).1 ha1
      linarith
    have hc2 := pow_le_pow_left₀ (norm_nonneg _) (norm_cfac_le lam κ hθ hv.1.le hv.2) 2
    have hgsq : (g v) ^ 2 = cm ^ 2 * C0 ^ 2 * M ^ 2 * ((θ + 1) / (v - θ)) := by
      rw [hg]
      simp only
      rw [mul_pow, hK, ← Real.rpow_natCast ((v - θ) ^ (-(1 / 2 : ℝ))) 2,
        ← Real.rpow_mul hvθ.le]
      have e1 : (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 := by push_cast; ring
      rw [e1, Real.rpow_neg_one]
      have : Real.sqrt (θ + 1) ^ 2 = θ + 1 := Real.sq_sqrt (by linarith)
      have e2 : (cm * C0 * M * Real.sqrt (θ + 1)) ^ 2 = cm ^ 2 * C0 ^ 2 * M ^ 2 * (θ + 1) := by
        rw [mul_pow, this]; ring
      rw [e2]; field_simp
    rw [hgsq]
    have hE0 : 0 ≤ B0121.graphNormSq (j + 1)
        ⟨expD (Real.log v - Real.log θ) (B0012.L0 (W v)), hEm⟩ := by
      unfold B0121.graphNormSq; positivity
    have hstep : B0121.graphNormSq (j + 1)
        ⟨expD (Real.log v - Real.log θ) (B0012.L0 (W v)), hEm⟩ ≤
        (θ + 1) / (v - θ) * (C0 ^ 2 * M ^ 2) :=
      hEb.trans (mul_le_mul hinv hG (by unfold B0121.graphNormSq; positivity)
        (by positivity))
    calc ‖cfac lam κ θ v‖ ^ 2 * B0121.graphNormSq (j + 1)
          ⟨expD (Real.log v - Real.log θ) (B0012.L0 (W v)), hEm⟩
        ≤ cm ^ 2 * ((θ + 1) / (v - θ) * (C0 ^ 2 * M ^ 2)) :=
          mul_le_mul hc2 hstep hE0 (by positivity)
      _ = _ := by ring
  obtain ⟨hmem, hb⟩ := graphIntegralBound (j + 1) θ (θ + 1) (by linarith) _ g hint hgint hbd
  refine ⟨hmem, hb.trans ?_⟩
  have hI : ∫ v in θ..θ + 1, g v = 2 * K := by
    rw [hg]
    simp only
    rw [intervalIntegral.integral_const_mul, integral_rpow_neg_half]; ring
  rw [hI]
  have hs : Real.sqrt (θ + 1) = (1 + θ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, add_comm]
  have hle : 2 * K ≤ (2 * cm * C0 + 1) * (1 + θ) ^ (1 / 2 : ℝ) * M := by
    rw [hK, hs]
    have : 0 ≤ (1 + θ) ^ (1 / 2 : ℝ) * M := by positivity
    nlinarith
  exact pow_le_pow_left₀ (by positivity) hle 2

end UnforcedLeray.Short.PartI
