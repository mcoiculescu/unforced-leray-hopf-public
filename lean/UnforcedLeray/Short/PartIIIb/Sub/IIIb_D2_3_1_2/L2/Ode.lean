import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2

/-!
# ODE for `Ψ = ∫_t^∞ (4πa)^{-3/2} e^{-r/a} da` (`PartIII-b:IIIb-D2/3/1/2/2`)

Source 3600-3610: `Δ ∫_t^∞ G = -G_t`, i.e. for `Ψ(|x|²/4)`: `rΨ'' + (3/2)Ψ' = -(4πt)^{-3/2}e^{-r/t}`
and its `r`-derivative `rΨ''' + (5/2)Ψ'' = (4πt)^{-3/2} t⁻¹ e^{-r/t}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `H_r(a) = (4πa)^{-3/2} e^{-r/a}`. -/
def OdeH (r a : ℝ) : ℝ := (4 * Real.pi * a) ^ (-3 / 2 : ℝ) * Real.exp (-r / a)

lemma ode_hasDeriv (r a : ℝ) (ha : 0 < a) :
    HasDerivAt (OdeH r) (r * L2hkG 2 a r + (3 / 2) * L2hkG 1 a r) a := by
  have h1 : HasDerivAt (fun a : ℝ => (4 * Real.pi * a) ^ (-3 / 2 : ℝ))
      ((4 * Real.pi) * (-3 / 2 : ℝ) * (4 * Real.pi * a) ^ (-3 / 2 - 1 : ℝ)) a := by
    have hl : HasDerivAt (fun a : ℝ => 4 * Real.pi * a) (4 * Real.pi) a := by
      simpa using (hasDerivAt_id a).const_mul (4 * Real.pi)
    exact hl.rpow_const (Or.inl (by positivity))
  have h2 : HasDerivAt (fun a : ℝ => Real.exp (-r / a)) (Real.exp (-r / a) * (r / a ^ 2)) a := by
    have hi : HasDerivAt (fun a : ℝ => -r / a) (r / a ^ 2) a := by
      have := (hasDerivAt_const a (-r)).div (hasDerivAt_id a) ha.ne'
      refine this.congr_deriv ?_
      simp
    exact hi.exp
  have h := h1.mul h2
  show HasDerivAt (fun a : ℝ => (4 * Real.pi * a) ^ (-3 / 2 : ℝ) * Real.exp (-r / a)) _ a
  refine h.congr_deriv ?_
  unfold L2hkG
  have e : (4 * Real.pi * a) ^ (-3 / 2 - 1 : ℝ) = (4 * Real.pi * a) ^ (-3 / 2 : ℝ) / (4 * Real.pi * a) := by
    rw [Real.rpow_sub (by positivity), Real.rpow_one]
  rw [e]
  have : (4 * Real.pi * a) ≠ 0 := by positivity
  have : a ≠ 0 := ha.ne'
  field_simp
  ring

lemma ode_tendsto (r : ℝ) : Tendsto (OdeH r) atTop (𝓝 0) := by
  have h1 : Tendsto (fun a : ℝ => (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := 3 / 2) (by norm_num)).comp
      (tendsto_id.const_mul_atTop (show 0 < 4 * Real.pi by positivity))
    simp only [neg_div]
    exact this
  have h2 : Tendsto (fun a : ℝ => Real.exp (-r / a)) atTop (𝓝 1) := by
    have h : Tendsto (fun a : ℝ => -r / a) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have := (Real.continuous_exp.tendsto 0).comp h
    simpa [Function.comp_def] using this
  have := h1.mul h2
  rw [zero_mul] at this
  exact this

lemma psi_ode (t : ℝ) (ht : 0 < t) (r : ℝ) :
    r * L2hkPsi t 2 r + (3 / 2) * L2hkPsi t 1 r = -OdeH r t := by
  have hint : ∀ (j : ℕ) (x : ℝ), Integrable (fun a => L2hkG j a x) (volume.restrict (Ioi t)) := by
    intro j x
    have hmeas : AEStronglyMeasurable (fun a => L2hkG j a x) (volume.restrict (Ioi t)) := by
      refine Measurable.aestronglyMeasurable ?_
      unfold L2hkG
      fun_prop
    refine Integrable.mono' (L2_intPow t ht ((1 / t) ^ j * Real.exp (|x| / t))) hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact L2_bound t ht j |x| a x (le_of_lt (Set.mem_Ioi.mp ha)) le_rfl
  have hsum : r * L2hkPsi t 2 r + (3 / 2) * L2hkPsi t 1 r =
      ∫ a in Ioi t, (r * L2hkG 2 a r + (3 / 2) * L2hkG 1 a r) := by
    unfold L2hkPsi
    rw [integral_add ((hint 2 r).const_mul r) ((hint 1 r).const_mul (3 / 2)),
      integral_const_mul, integral_const_mul]
  rw [hsum]
  have hder : ∀ a ∈ Ioi t, HasDerivAt (OdeH r) (r * L2hkG 2 a r + (3 / 2) * L2hkG 1 a r) a :=
    fun a ha => ode_hasDeriv r a (lt_trans ht ha)
  have hcont : ContinuousWithinAt (OdeH r) (Ici t) t := by
    have : ContinuousAt (OdeH r) t := (ode_hasDeriv r t ht).continuousAt
    exact this.continuousWithinAt
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont hder
    (((hint 2 r).const_mul r).add ((hint 1 r).const_mul (3 / 2))) (ode_tendsto r)
  rw [this]
  ring

lemma psi_ode_deriv (t : ℝ) (ht : 0 < t) (r : ℝ) :
    r * L2hkPsi t 3 r + (5 / 2) * L2hkPsi t 2 r =
      (4 * Real.pi * t) ^ (-3 / 2 : ℝ) * t⁻¹ * Real.exp (-r / t) := by
  have hL : HasDerivAt (fun r => r * L2hkPsi t 2 r + (3 / 2) * L2hkPsi t 1 r)
      (L2hkPsi t 2 r + r * L2hkPsi t 3 r + (3 / 2) * L2hkPsi t 2 r) r :=
    (((hasDerivAt_id r).mul (L2_psi_hasDeriv t ht 2 r)).add
      ((L2_psi_hasDeriv t ht 1 r).const_mul (3 / 2))).congr_deriv (by simp)
  have hR : HasDerivAt (fun r => -OdeH r t)
      ((4 * Real.pi * t) ^ (-3 / 2 : ℝ) * t⁻¹ * Real.exp (-r / t)) r := by
    unfold OdeH
    have hi : HasDerivAt (fun r : ℝ => -r / t) (-t⁻¹) r := by
      have := ((hasDerivAt_id r).neg).div_const t
      refine this.congr_deriv ?_
      simp [div_eq_mul_inv]
    have := (hi.exp.const_mul ((4 * Real.pi * t) ^ (-3 / 2 : ℝ))).neg
    show HasDerivAt (fun r : ℝ => -((4 * Real.pi * t) ^ (-3 / 2 : ℝ) * Real.exp (-r / t))) _ r
    refine this.congr_deriv ?_
    ring
  have hfun : (fun r => r * L2hkPsi t 2 r + (3 / 2) * L2hkPsi t 1 r) = fun r => -OdeH r t :=
    funext (psi_ode t ht)
  rw [hfun] at hL
  have := hL.unique hR
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
