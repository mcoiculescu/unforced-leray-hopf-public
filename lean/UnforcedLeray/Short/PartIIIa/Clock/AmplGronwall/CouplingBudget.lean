import UnforcedLeray.Short.PartIIIa.Clock.AmplGronwall.MovingExp

/-!
# Part III-a, task `PartIII-a:T21/c4/3`: the initial-complement coupling budget

Source: `the November 2 reference manuscript` lines 3005-3010 (the initial-complement
term is integrable with bound `C‖r(t)‖/b`).

Proves `AmplCouplingBudget` with `K₁ := C²(1+C)/h₀`. On `Ioc t s`, with `θ_r = clockTheta ν r`,
`1/θ_r = ν·clockA ν r`. From `1 ≤ b ≤ θ_s` we get `ν·clockA ν s ≤ 1`, hence
`ν·clockA ν r ≤ 1` for `r ≤ s`, and `ν³ ≤ 1`. So `C(1/θ_r + Cν³/θ_r) ≤ C(1+C)`, and the integrand
is bounded by `C²(1+C) · a⁻² e^{-h₀(z(r)-z(t))}`. The integral of the latter is `≤ 1/h₀` by
`movingExpIntegral` (`T21/c4/1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem amplCouplingBudget : UnforcedLeray.Short.IIIa.AmplCouplingBudget := by
  unfold AmplCouplingBudget
  intro C h₀ hC hh₀
  refine ⟨C ^ 2 * (1 + C) / h₀, ?_⟩
  intro b hb ν hν t s ht hts hbs
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2
  have hK : (0 : ℝ) ≤ C ^ 2 * (1 + C) := mul_nonneg (sq_nonneg C) (by linarith)
  have hAs : 0 < clockA ν s := by
    unfold clockA
    nlinarith [mul_nonneg hν0.le (ht.trans hts)]
  have hps : 0 < ν * clockA ν s := mul_pos hν0 hAs
  have hθs1 : 1 ≤ clockTheta ν s := le_trans hb hbs
  have hps1 : ν * clockA ν s ≤ 1 := by
    unfold clockTheta at hθs1
    have h2 := mul_inv_cancel₀ hps.ne'
    nlinarith [mul_le_mul_of_nonneg_left hθs1 hps.le]
  have hpt : ∀ r ∈ Ioc t s,
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
        (ENNReal.ofReal (C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)) *
          ENNReal.ofReal (C * Real.exp (-h₀ * (movingZ ν r - movingZ ν t))))
      ≤ ENNReal.ofReal (C ^ 2 * (1 + C)) *
        ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
          Real.exp (-h₀ * (movingZ ν r - movingZ ν t))) := by
    intro r hr
    have hr0 : 0 ≤ r := ht.trans hr.1.le
    have hAr : 0 < clockA ν r := by
      unfold clockA
      nlinarith [mul_nonneg hν0.le hr0]
    have hle : ν * clockA ν r ≤ ν * clockA ν s := by
      unfold clockA
      nlinarith [mul_le_mul_of_nonneg_left hr.2 (mul_nonneg hν0.le hν0.le)]
    have hule : ν * clockA ν r ≤ 1 := le_trans hle hps1
    have hu0 : 0 ≤ ν * clockA ν r := (mul_pos hν0 hAr).le
    have hu : (clockTheta ν r)⁻¹ = ν * clockA ν r := by
      unfold clockTheta
      rw [inv_inv]
    have hθinv : 1 / clockTheta ν r = ν * clockA ν r := by
      rw [one_div, hu]
    have hθinv' : C * ν ^ 3 / clockTheta ν r = C * ν ^ 3 * (ν * clockA ν r) := by
      rw [div_eq_mul_inv, hu]
    have hν3 : 0 ≤ ν ^ 3 := pow_nonneg hν0.le 3
    have hν3le : ν ^ 3 ≤ 1 := pow_le_one₀ hν0.le hν1
    have hA2 : 0 ≤ (clockA ν r) ^ (-2 : ℝ) := Real.rpow_nonneg hAr.le _
    have hE : 0 ≤ Real.exp (-h₀ * (movingZ ν r - movingZ ν t)) := (Real.exp_pos _).le
    have hcub : ν ^ 3 * (ν * clockA ν r) ≤ 1 := by
      calc ν ^ 3 * (ν * clockA ν r) ≤ 1 * 1 := mul_le_mul hν3le hule hu0 zero_le_one
        _ = 1 := by norm_num
    have h1 : C * ν ^ 3 * (ν * clockA ν r) ≤ C := by
      have h3 := mul_le_mul_of_nonneg_left hcub hC.le
      calc C * ν ^ 3 * (ν * clockA ν r) = C * (ν ^ 3 * (ν * clockA ν r)) := by ring
        _ ≤ C * 1 := h3
        _ = C := by ring
    have hin : ν * clockA ν r + C * ν ^ 3 * (ν * clockA ν r) ≤ 1 + C := by
      linarith
    have hXle : C * (ν * clockA ν r + C * ν ^ 3 * (ν * clockA ν r)) ≤ C * (1 + C) :=
      mul_le_mul_of_nonneg_left hin hC.le
    have hX : 0 ≤ C * (ν * clockA ν r + C * ν ^ 3 * (ν * clockA ν r)) :=
      mul_nonneg hC.le (add_nonneg hu0 (mul_nonneg (mul_nonneg hC.le hν3) hu0))
    rw [hθinv, hθinv']
    set X := C * (ν * clockA ν r + C * ν ^ 3 * (ν * clockA ν r)) with hXd
    set A2 := (clockA ν r) ^ (-2 : ℝ) with hA2d
    set E := Real.exp (-h₀ * (movingZ ν r - movingZ ν t)) with hEd
    have h3 : X * (C * E) ≤ C * (1 + C) * (C * E) :=
      mul_le_mul_of_nonneg_right hXle (mul_nonneg hC.le hE)
    have h4 : A2 * (X * (C * E)) ≤ A2 * (C * (1 + C) * (C * E)) :=
      mul_le_mul_of_nonneg_left h3 hA2
    have key : A2 * (X * (C * E)) ≤ C ^ 2 * (1 + C) * (A2 * E) := by
      calc A2 * (X * (C * E)) ≤ A2 * (C * (1 + C) * (C * E)) := h4
        _ = C ^ 2 * (1 + C) * (A2 * E) := by ring
    calc ENNReal.ofReal A2 * (ENNReal.ofReal X * ENNReal.ofReal (C * E))
        = ENNReal.ofReal (A2 * (X * (C * E))) := by
          rw [ENNReal.ofReal_mul hA2, ENNReal.ofReal_mul hX]
      _ ≤ ENNReal.ofReal (C ^ 2 * (1 + C) * (A2 * E)) := ENNReal.ofReal_le_ofReal key
      _ = ENNReal.ofReal (C ^ 2 * (1 + C)) * ENNReal.ofReal (A2 * E) := by
          rw [ENNReal.ofReal_mul hK]
  have hexp := movingExpIntegral ν h₀ t s hν0 hh₀ ht hts
  refine le_trans (setLIntegral_mono' measurableSet_Ioc hpt) ?_
  rw [lintegral_const_mul' (ENNReal.ofReal (C ^ 2 * (1 + C))) _ ENNReal.ofReal_ne_top]
  refine le_trans (b := ENNReal.ofReal (C ^ 2 * (1 + C)) * ENNReal.ofReal (1 / h₀)) ?_ ?_
  · gcongr
  · rw [← ENNReal.ofReal_mul hK]
    apply ENNReal.ofReal_le_ofReal
    exact le_of_eq (by ring)

end UnforcedLeray.Short.IIIa
