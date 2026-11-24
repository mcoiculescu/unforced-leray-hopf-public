import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11_3_3

/-!
# `PartIII-b:C/inst/11/3/3/3`: one Gaussian integral, uniform in `a ∈ [1, 21/10]`

Source `shorter-proof-2026-11-02.tex` lines 5063-5079 (one Gaussian integral in the Cauchy-Schwarz
step).
Write `P(t) = (1+|t|)^8 e^{-(5/28)t²}`. For `a ∈ [1, 21/10]` and `y = (y₁, y₂)` the integrand
satisfies `(1+‖y‖)^8 e^{-(3/8)|y|²/a} ≤ P(y₁) P(y₂)`, because `1+‖y‖ ≤ (1+|y₁|)(1+|y₂|)` and
`(3/8)/a ≥ 5/28`. The plane integral then factorises (`lintegral_prod_mul`) into `(∫⁻ P)²`,
and `∫⁻ P < ∞` since `P ≤ e^{896/5} e^{-(5/56)t²}` (AM-GM: `8|t| ≤ (5/56)t² + 896/5`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- One-dimensional profile `(1+|t|)^8 e^{-(5/28)t²}`. -/
def gi8Prof (t : ℝ) : ℝ := (1 + |t|) ^ 8 * Real.exp (-(5 / 28) * t ^ 2)

theorem gi8Prof_nonneg (t : ℝ) : 0 ≤ gi8Prof t := by
  unfold gi8Prof
  positivity

theorem gi8Prof_meas : Measurable gi8Prof :=
  Continuous.measurable (by unfold gi8Prof; fun_prop)

theorem gi8Prof_integrable : MeasureTheory.Integrable gi8Prof := by
  have hg : Integrable (fun t : ℝ => Real.exp (896 / 5) * Real.exp (-(5 / 56) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 5 / 56)).const_mul _
  refine hg.mono' gi8Prof_meas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  rw [Real.norm_of_nonneg (gi8Prof_nonneg t)]
  unfold gi8Prof
  have h1 : (1 + |t|) ≤ Real.exp |t| := by linarith [Real.add_one_le_exp |t|]
  have h2 : (1 + |t|) ^ 8 ≤ Real.exp (8 * |t|) := by
    rw [show (8 : ℝ) * |t| = ((8 : ℕ) : ℝ) * |t| by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) h1 8
  have h3 : 8 * |t| ≤ (5 / 56) * t ^ 2 + 896 / 5 := by
    nlinarith [sq_nonneg ((5 / 56) * |t| - 4), sq_abs t, abs_nonneg t]
  have e : Real.exp ((5 / 56) * t ^ 2) * Real.exp (-(5 / 28) * t ^ 2)
      = Real.exp (-(5 / 56) * t ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (1 + |t|) ^ 8 * Real.exp (-(5 / 28) * t ^ 2)
      ≤ Real.exp (8 * |t|) * Real.exp (-(5 / 28) * t ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ ≤ Real.exp ((5 / 56) * t ^ 2 + 896 / 5) * Real.exp (-(5 / 28) * t ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h3) (Real.exp_pos _).le
    _ = Real.exp (896 / 5) * (Real.exp ((5 / 56) * t ^ 2) * Real.exp (-(5 / 28) * t ^ 2)) := by
        rw [Real.exp_add]
        ring
    _ = Real.exp (896 / 5) * Real.exp (-(5 / 56) * t ^ 2) := by rw [e]

/-- Pointwise domination of the integrand by a product of one-dimensional profiles. -/
theorem gi8_bound_pt (a : ℝ) (ha1 : 1 ≤ a) (ha2 : a ≤ 21 / 10) (y : ℝ × ℝ) :
    (1 + ‖y‖) ^ 8 * Real.exp (-(3 / 8) * sq2 y / a) ≤ gi8Prof y.1 * gi8Prof y.2 := by
  have hn : 1 + ‖y‖ ≤ (1 + |y.1|) * (1 + |y.2|) := by
    rw [Prod.norm_def]
    simp only [Real.norm_eq_abs]
    rcases max_choice |y.1| |y.2| with h | h <;> rw [h] <;>
      nlinarith [abs_nonneg y.1, abs_nonneg y.2]
  have hpow : (1 + ‖y‖) ^ 8 ≤ (1 + |y.1|) ^ 8 * (1 + |y.2|) ^ 8 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hn 8
  have hS : 0 ≤ sq2 y := by
    unfold sq2
    positivity
  have hkey : (5 / 28) * sq2 y ≤ (3 / 8) * sq2 y / a := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg hS (show (0 : ℝ) ≤ 21 / 10 - a by linarith)]
  have hexp : Real.exp (-(3 / 8) * sq2 y / a)
      ≤ Real.exp (-(5 / 28) * y.1 ^ 2) * Real.exp (-(5 / 28) * y.2 ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have e : -(3 / 8) * sq2 y / a = -((3 / 8) * sq2 y / a) := by ring
    rw [e]
    unfold sq2 at hkey ⊢
    linarith
  calc (1 + ‖y‖) ^ 8 * Real.exp (-(3 / 8) * sq2 y / a)
      ≤ ((1 + |y.1|) ^ 8 * (1 + |y.2|) ^ 8) *
          (Real.exp (-(5 / 28) * y.1 ^ 2) * Real.exp (-(5 / 28) * y.2 ^ 2)) :=
        mul_le_mul hpow hexp (by positivity) (by positivity)
    _ = gi8Prof y.1 * gi8Prof y.2 := by
        unfold gi8Prof
        ring

theorem gaussInt8 : GaussInt8 := by
  have hM : (∫⁻ t : ℝ, ENNReal.ofReal (gi8Prof t)) ≠ ⊤ :=
    gi8Prof_integrable.lintegral_lt_top.ne
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (gi8Prof t)) :=
    gi8Prof_meas.ennreal_ofReal
  refine ⟨(∫⁻ t : ℝ, ENNReal.ofReal (gi8Prof t)).toReal ^ 2, sq_nonneg _, fun a ha1 ha2 => ?_⟩
  calc ∫⁻ y : ℝ × ℝ, ENNReal.ofReal ((1 + ‖y‖) ^ 8 * Real.exp (-(3 / 8) * sq2 y / a))
      ≤ ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (gi8Prof y.1) * ENNReal.ofReal (gi8Prof y.2) := by
        apply lintegral_mono
        intro y
        dsimp only
        rw [← ENNReal.ofReal_mul (gi8Prof_nonneg y.1)]
        exact ENNReal.ofReal_le_ofReal (gi8_bound_pt a ha1 ha2 y)
    _ = (∫⁻ t : ℝ, ENNReal.ofReal (gi8Prof t)) * ∫⁻ t : ℝ, ENNReal.ofReal (gi8Prof t) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_mul hm.aemeasurable hm.aemeasurable
    _ = ENNReal.ofReal ((∫⁻ t : ℝ, ENNReal.ofReal (gi8Prof t)).toReal ^ 2) := by
        rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hM, sq]

end UnforcedLeray.Short.PartIIIb.Concrete
