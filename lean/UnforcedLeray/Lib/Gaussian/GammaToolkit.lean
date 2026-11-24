import UnforcedLeray.Analysis.Pressure.NewtonIdentity

/-!
# Gamma-type integral toolkit (INF22 G4)


and §5 target G4. Built on the compiled `UnforcedLeray.PressureAnalysis.integral_inverseTimeGamma`
(`lean/UnforcedLeray/Analysis/Pressure/NewtonIdentity.lean:54`) and Mathlib's
`Real.integral_rpow_mul_exp_neg_mul_Ioi`.

Main results:
* `integral_rpow_mul_exp_neg_mul` (B0384, B0863; tex 6979–6988, 12875–12887):
  `∫_0^∞ s^σ e^{-bs} ds = Γ(σ+1) b^{-σ-1}` for `σ > -1`, `b > 0`;
* `integral_inverseTime_window_le` (B0154, B0158; tex 2348–2353, 2394–2404):
  `∫_1^{c²} a^{-k} e^{-bc²/a} da ≤ Γ(k-1) b^{1-k} (c²)^{1-k}` for `k > 1`, `b > 0`, `c ≠ 0`
  (`(c²)^{1-k}` is the manuscript's `c^{2-2k}`, written so that no rpow of a negative base
  occurs);
* `integral_one_add_rpow_mul_exp_le` (B0339; tex 6404–6428):
  `∫_0^∞ (1+u)^M e^{-bu} du ≤ C_M b^{-1}(1 + b^{-M})` for `M ≥ 0`, `b > 0`, with
  `C_M = 2^M (1 + Γ(M+1))` independent of `b`; integrability in
  `integrableOn_one_add_rpow_mul_exp`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open MeasureTheory Real Set

/-- `s^σ e^{-bs}` is integrable on `(0, ∞)` for `σ > -1`, `b > 0`. -/
theorem integrableOn_rpow_mul_exp_neg_mul {σ b : ℝ} (hσ : -1 < σ) (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => s ^ σ * Real.exp (-b * s)) (Ioi 0) := by
  simpa only [Real.rpow_one] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := σ) (b := b) hσ one_pos hb

/-- **G4 (B0384, B0863).** `∫_0^∞ s^σ e^{-bs} ds = Γ(σ+1) b^{-σ-1}`. -/
theorem integral_rpow_mul_exp_neg_mul {σ b : ℝ} (hσ : -1 < σ) (hb : 0 < b) :
    ∫ s in Ioi (0 : ℝ), s ^ σ * Real.exp (-b * s) = Real.Gamma (σ + 1) * b ^ (-σ - 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := σ + 1) (r := b) (by linarith) hb
  simp only [add_sub_cancel_right, neg_mul] at h
  simp only [neg_mul]
  rw [h, one_div, Real.inv_rpow hb.le, ← Real.rpow_neg hb.le, mul_comm]
  congr 2; ring

/-- **G4 (B0154, B0158).** `∫_1^{c²} a^{-k} e^{-bc²/a} da ≤ Γ(k-1) b^{1-k} (c²)^{1-k}` for
`k > 1`, `b > 0`, `c ≠ 0` (the interval integral; if `c² < 1` it is `≤ 0`). -/
theorem integral_inverseTime_window_le {k b c : ℝ} (hk : 1 < k) (hb : 0 < b) (hc : c ≠ 0) :
    ∫ a in (1 : ℝ)..c ^ 2, a ^ (-k) * Real.exp (-b * c ^ 2 / a) ≤
      Real.Gamma (k - 1) * b ^ (1 - k) * (c ^ 2) ^ (1 - k) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hB : 0 < b * c ^ 2 := by positivity
  have hRHS : 0 ≤ Real.Gamma (k - 1) * b ^ (1 - k) * (c ^ 2) ^ (1 - k) :=
    mul_nonneg (mul_nonneg (Real.Gamma_pos_of_pos (by linarith)).le (by positivity))
      (by positivity)
  have hfeq : ∀ a : ℝ, a ^ (-k) * Real.exp (-b * c ^ 2 / a) =
      a ^ (-((k - 1) + 1)) * Real.exp (-(b * c ^ 2) / a) := by
    intro a; congr 2 <;> ring
  have hint := PressureAnalysis.integrableOn_inverseTimeGamma hB (show 0 < k - 1 by linarith)
  have hval := PressureAnalysis.integral_inverseTimeGamma hB (show 0 < k - 1 by linarith)
  rcases le_total 1 (c ^ 2) with h1 | h1
  · rw [intervalIntegral.integral_of_le h1]
    simp_rw [hfeq]
    calc ∫ a in Ioc 1 (c ^ 2), a ^ (-((k - 1) + 1)) * Real.exp (-(b * c ^ 2) / a)
        ≤ ∫ a in Ioi 0, a ^ (-((k - 1) + 1)) * Real.exp (-(b * c ^ 2) / a) := by
          refine setIntegral_mono_set hint ?_ ?_
          · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall
              fun a ha => ?_)
            exact mul_nonneg (Real.rpow_pos_of_pos ha _).le (Real.exp_pos _).le
          · exact (Filter.Eventually.of_forall fun a ha => lt_of_lt_of_le one_pos ha.1.le :
              ∀ᵐ a ∂volume, a ∈ Ioc (1 : ℝ) (c ^ 2) → a ∈ Ioi 0)
      _ = (b * c ^ 2) ^ (-(k - 1)) * Real.Gamma (k - 1) := hval
      _ = Real.Gamma (k - 1) * b ^ (1 - k) * (c ^ 2) ^ (1 - k) := by
          rw [Real.mul_rpow hb.le hc2.le, show -(k - 1) = 1 - k by ring]; ring
  · rw [intervalIntegral.integral_of_ge h1]
    refine le_trans ?_ hRHS
    rw [neg_nonpos]
    refine setIntegral_nonneg measurableSet_Ioc fun a ha => ?_
    exact mul_nonneg (Real.rpow_pos_of_pos (lt_of_lt_of_le hc2 ha.1.le) _).le (Real.exp_pos _).le

/-- `(1+u)^M ≤ 2^M (1 + u^M)` for `u ≥ 0`, `M ≥ 0`. -/
theorem one_add_rpow_le {M u : ℝ} (hM : 0 ≤ M) (hu : 0 ≤ u) :
    (1 + u) ^ M ≤ 2 ^ M * (1 + u ^ M) := by
  have h2 : (0 : ℝ) ≤ 2 ^ M := by positivity
  have huM : 0 ≤ u ^ M := by positivity
  rcases le_total u 1 with h | h
  · have : (1 + u) ^ M ≤ 2 ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
    nlinarith
  · have : (1 + u) ^ M ≤ (2 * u) ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
    rw [Real.mul_rpow (by norm_num) hu] at this
    nlinarith

theorem integrableOn_one_add_rpow_mul_exp {M b : ℝ} (hM : 0 ≤ M) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => (1 + u) ^ M * Real.exp (-b * u)) (Ioi 0) := by
  have h0 := integrableOn_rpow_mul_exp_neg_mul (σ := 0) (by norm_num) hb
  have hM' := integrableOn_rpow_mul_exp_neg_mul (σ := M) (by linarith) hb
  have hsum : IntegrableOn (fun u : ℝ => 2 ^ M * (u ^ (0 : ℝ) * Real.exp (-b * u) +
      u ^ M * Real.exp (-b * u))) (Ioi 0) := (h0.add hM').const_mul _
  refine hsum.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le),
    Real.rpow_zero, one_mul]
  have := one_add_rpow_le hM hu0
  have he := (Real.exp_pos (-b * u)).le
  nlinarith

/-- **G4 (B0339).** `∫_0^∞ (1+u)^M e^{-bu} du ≤ C_M b^{-1}(1 + b^{-M})`,
`C_M = 2^M (1 + Γ(M+1))`, for `M ≥ 0`, `b > 0`. -/
theorem integral_one_add_rpow_mul_exp_le {M b : ℝ} (hM : 0 ≤ M) (hb : 0 < b) :
    ∫ u in Ioi (0 : ℝ), (1 + u) ^ M * Real.exp (-b * u) ≤
      2 ^ M * (1 + Real.Gamma (M + 1)) * (b⁻¹ * (1 + b ^ (-M))) := by
  have h0 := integrableOn_rpow_mul_exp_neg_mul (σ := 0) (by norm_num) hb
  have hM' := integrableOn_rpow_mul_exp_neg_mul (σ := M) (by linarith) hb
  have hle : ∫ u in Ioi (0 : ℝ), (1 + u) ^ M * Real.exp (-b * u) ≤
      ∫ u in Ioi (0 : ℝ), 2 ^ M * (u ^ (0 : ℝ) * Real.exp (-b * u) +
        u ^ M * Real.exp (-b * u)) := by
    refine setIntegral_mono_on (integrableOn_one_add_rpow_mul_exp hM hb)
      ((h0.add hM').const_mul _) measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 ≤ u := le_of_lt hu
    rw [Real.rpow_zero, one_mul]
    have := one_add_rpow_le hM hu0
    have he := (Real.exp_pos (-b * u)).le
    nlinarith
  have hval : ∫ u in Ioi (0 : ℝ), 2 ^ M * (u ^ (0 : ℝ) * Real.exp (-b * u) +
        u ^ M * Real.exp (-b * u)) = 2 ^ M * (b⁻¹ + Real.Gamma (M + 1) * b ^ (-M - 1)) := by
    rw [integral_const_mul, integral_add h0 hM', integral_rpow_mul_exp_neg_mul (by norm_num) hb,
      integral_rpow_mul_exp_neg_mul (by linarith) hb]
    simp [Real.Gamma_one, Real.rpow_neg_one]
  refine hle.trans (hval.le.trans ?_)
  · have hG : 0 < Real.Gamma (M + 1) := Real.Gamma_pos_of_pos (by linarith)
    have hbM : b ^ (-M - 1) = b⁻¹ * b ^ (-M) := by
      rw [show -M - 1 = -1 + -M by ring, Real.rpow_add hb, Real.rpow_neg_one]
    have hbinv : 0 < b⁻¹ := inv_pos.2 hb
    have hbM0 : 0 < b ^ (-M) := Real.rpow_pos_of_pos hb _
    have h2 : 0 < (2 : ℝ) ^ M := by positivity
    rw [hbM]
    have : b⁻¹ + Real.Gamma (M + 1) * (b⁻¹ * b ^ (-M)) ≤
        (1 + Real.Gamma (M + 1)) * (b⁻¹ * (1 + b ^ (-M))) := by nlinarith
    calc 2 ^ M * (b⁻¹ + Real.Gamma (M + 1) * (b⁻¹ * b ^ (-M)))
        ≤ 2 ^ M * ((1 + Real.Gamma (M + 1)) * (b⁻¹ * (1 + b ^ (-M)))) := by gcongr
      _ = _ := by ring

end UnforcedLeray.Gaussian
