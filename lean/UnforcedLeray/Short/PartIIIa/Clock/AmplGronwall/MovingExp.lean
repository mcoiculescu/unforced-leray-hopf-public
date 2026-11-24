import UnforcedLeray.Short.PartIIIa.Sub.T21_c4

/-!
# Part III-a, task `PartIII-a:T21/c4/1`: the moving exponential integral

Source: `the November 2 reference manuscript` lines 2855 (`z = s/a(s)`,
`dz = ds/a²`) and 3005-3010. Proves `MovingExpIntegral` from `Sub/T21_c4.lean`:
`∫_t^s a⁻² e^{-h₀(z(r)-z(t))} dr ≤ 1/h₀`, by the antiderivative
`F(r) = -(1/h₀) e^{-h₀(z(r)-z(t))}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem movingExpIntegral : UnforcedLeray.Short.IIIa.MovingExpIntegral := by
  unfold MovingExpIntegral
  intro ν h₀ t s hν hh₀ ht hts
  have hν0 : 0 < ν := hν
  have hh0 : h₀ ≠ 0 := hh₀.ne'
  have hApos : ∀ r : ℝ, 0 ≤ r → 0 < clockA ν r := fun r hr => by
    unfold clockA
    linarith [mul_nonneg hν0.le hr]
  -- derivative of z = movingZ ν
  have hderiv_z : ∀ r : ℝ, 0 ≤ r →
      HasDerivAt (fun τ => movingZ ν τ) ((clockA ν r) ^ (-2 : ℝ)) r := by
    intro r hr
    have h0 : (1 + ν * r) ≠ 0 := (hApos r hr).ne'
    have h1 : HasDerivAt (fun τ : ℝ => 1 + ν * τ) ν r := by
      simpa using ((hasDerivAt_id r).const_mul ν).const_add 1
    have h2 : HasDerivAt (fun τ : ℝ => τ / (1 + ν * τ))
        ((1 * (1 + ν * r) - r * ν) / (1 + ν * r) ^ 2) r :=
      (hasDerivAt_id' r).div h1 h0
    have e : (1 * (1 + ν * r) - r * ν) = (1 : ℝ) := by ring
    have h3 : (clockA ν r) ^ (-2 : ℝ) = (1 * (1 + ν * r) - r * ν) / (1 + ν * r) ^ 2 := by
      rw [Real.rpow_neg (hApos r hr).le, Real.rpow_two, e]
      unfold clockA
      rw [one_div]
    rw [h3]
    exact h2
  -- derivative of the antiderivative F
  have hF : ∀ r : ℝ, 0 ≤ r → HasDerivAt
      (fun τ => -(1 / h₀) * Real.exp (-h₀ * (movingZ ν τ - movingZ ν t)))
      ((clockA ν r) ^ (-2 : ℝ) * Real.exp (-h₀ * (movingZ ν r - movingZ ν t))) r := by
    intro r hr
    have h1 := ((((hderiv_z r hr).sub_const (movingZ ν t)).const_mul (-h₀)).exp).const_mul
      (-(1 / h₀))
    refine h1.congr_deriv ?_
    have e : -(1 / h₀) * (-h₀) = (1 : ℝ) := by
      rw [neg_mul_neg, one_div_mul_cancel hh0]
    calc _ = (-(1 / h₀) * (-h₀)) *
          ((clockA ν r) ^ (-2 : ℝ) * Real.exp (-h₀ * (movingZ ν r - movingZ ν t))) := by ring
      _ = _ := by rw [e, one_mul]
  have hd : ∀ r ∈ uIcc t s,
      HasDerivAt (fun τ => -(1 / h₀) * Real.exp (-h₀ * (movingZ ν τ - movingZ ν t)))
        ((clockA ν r) ^ (-2 : ℝ) * Real.exp (-h₀ * (movingZ ν r - movingZ ν t))) r := by
    intro r hr
    rw [uIcc_of_le hts] at hr
    exact hF r (ht.trans hr.1)
  have hcont : ContinuousOn
      (fun τ => -(1 / h₀) * Real.exp (-h₀ * (movingZ ν τ - movingZ ν t))) (Icc t s) :=
    fun r hr => (hd r (by rw [uIcc_of_le hts]; exact hr)).continuousAt.continuousWithinAt
  have hnn : ∀ r ∈ Ioc t s,
      0 ≤ (clockA ν r) ^ (-2 : ℝ) * Real.exp (-h₀ * (movingZ ν r - movingZ ν t)) := fun r hr =>
    mul_nonneg (Real.rpow_nonneg (hApos r (ht.trans hr.1.le)).le _) (Real.exp_pos _).le
  have hI : IntegrableOn
      (fun r => (clockA ν r) ^ (-2 : ℝ) * Real.exp (-h₀ * (movingZ ν r - movingZ ν t)))
      (Ioc t s) :=
    intervalIntegral.integrableOn_deriv_of_nonneg (g' := fun r =>
        (clockA ν r) ^ (-2 : ℝ) * Real.exp (-h₀ * (movingZ ν r - movingZ ν t)))
      hcont (fun r hr => hd r (by rw [uIcc_of_le hts]; exact Set.Ioo_subset_Icc_self hr))
      (fun r hr => hnn r ⟨hr.1, hr.2.le⟩)
  have hIi : IntervalIntegrable
      (fun r => (clockA ν r) ^ (-2 : ℝ) * Real.exp (-h₀ * (movingZ ν r - movingZ ν t)))
      MeasureTheory.volume t s := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hts]
    exact hI
  have hFTC : ∫ r in t..s, (clockA ν r) ^ (-2 : ℝ) *
        Real.exp (-h₀ * (movingZ ν r - movingZ ν t))
      = -(1 / h₀) * Real.exp (-h₀ * (movingZ ν s - movingZ ν t)) -
        -(1 / h₀) * Real.exp (-h₀ * (movingZ ν t - movingZ ν t)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => hd r hr) hIi
  have hEt : Real.exp (-h₀ * (movingZ ν t - movingZ ν t)) = 1 := by
    rw [sub_self, mul_zero, Real.exp_zero]
  have hEs : 0 ≤ (1 / h₀) * Real.exp (-h₀ * (movingZ ν s - movingZ ν t)) :=
    mul_nonneg (one_div_pos.mpr hh₀).le (Real.exp_pos _).le
  have hconv : ∫⁻ r in Ioc t s, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
        Real.exp (-h₀ * (movingZ ν r - movingZ ν t)))
      = ENNReal.ofReal (∫ r in Ioc t s, (clockA ν r) ^ (-2 : ℝ) *
        Real.exp (-h₀ * (movingZ ν r - movingZ ν t))) :=
    (ofReal_integral_eq_lintegral_ofReal hI (ae_restrict_of_forall_mem measurableSet_Ioc
      (fun r hr => hnn r hr))).symm
  rw [hconv, ← intervalIntegral.integral_of_le hts, hFTC, hEt]
  apply ENNReal.ofReal_le_ofReal
  linarith [hEs]

end UnforcedLeray.Short.IIIa
