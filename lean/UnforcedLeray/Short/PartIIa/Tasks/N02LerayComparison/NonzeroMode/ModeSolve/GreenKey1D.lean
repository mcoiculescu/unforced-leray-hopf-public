import UnforcedLeray.Short.PartIIa.Sub.N02_4_5

/-!
# Part II-a, task `PartII-a:N02/4/5/1` (`NzGreenKey1D`): the one-dimensional Green identity

Source of record: `the November 2 reference manuscript`, lines 1713-1722.
Target: `NzGreenKey1D` in `Sub/N02_4_5.lean`.

Proof (fundamental theorem of calculus with explicit antiderivatives, no integration by parts).
Write `κ = |k| > 0`, `f = u'' - κ² u`. Then
* `A(s) = e^{κs} (u'(s) - κ u(s))` has `A' = e^{κs} f`,
* `B(s) = e^{-κs} (u'(s) + κ u(s))` has `B' = e^{-κs} f`,
* `A(s) = 0` for `s` very negative and `B(s) = 0` for `s` very positive (compact support).

Substituting `t ↦ η - t` and splitting at `s = η`, the Green kernel is
`-(e^{-κη}/(2κ)) e^{κs}` for `s ≤ η` and `-(e^{κη}/(2κ)) e^{-κs}` for `s ≥ η`. Hence
`∫ = -(e^{-κη}/(2κ)) A(η) + (e^{κη}/(2κ)) B(η) = -(u'(η) - κu(η))/(2κ) + (u'(η) + κu(η))/(2κ) = u(η)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-! ### Helpers -/

/-- Second iterated derivative as the derivative of the first. -/
theorem nzgk1_iter2 (u : ℝ → ℂ) : iteratedDeriv 2 u = deriv (deriv u) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- The first derivative of a `C²` function is differentiable. -/
theorem nzgk1_diff_deriv (u : ℝ → ℂ) (hu : ContDiff ℝ 2 u) : Differentiable ℝ (deriv u) := by
  have h := hu.differentiable_iteratedDeriv 1 (by norm_num)
  rwa [iteratedDeriv_one] at h

/-- Algebra: the two boundary terms combine to `u`. -/
theorem nzgk1_alg (p q c u0 u1 : ℂ) (hc : c ≠ 0) (hpq : p * q = 1) :
    -q / (2 * c) * (p * (u1 - c * u0)) + -p / (2 * c) * (0 - q * (u1 + c * u0)) = u0 := by
  have key : -q / (2 * c) * (p * (u1 - c * u0)) + -p / (2 * c) * (0 - q * (u1 + c * u0))
      = (p * q) * u0 := by
    field_simp
    ring
  rw [key, hpq, one_mul]

/-- Main computation for the one-dimensional Green identity, with `κ > 0` in place of `|k|`. -/
theorem nzgk1_main (κ : ℝ) (hκ : 0 < κ) (u : ℝ → ℂ) (hu : ContDiff ℝ 2 u)
    (hc : HasCompactSupport u) (η : ℝ) :
    ∫ s : ℝ, ((-Real.exp (-κ * |η - s|) / (2 * κ) : ℝ) : ℂ) *
      (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s) = u η := by
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdu : Differentiable ℝ (deriv u) := nzgk1_diff_deriv u hu
  have hI2 : iteratedDeriv 2 u = deriv (deriv u) := nzgk1_iter2 u
  have hcont2 : Continuous (iteratedDeriv 2 u) := hu.continuous_iteratedDeriv 2 (by norm_num)
  have hcs2 : HasCompactSupport (iteratedDeriv 2 u) := by
    rw [hI2]
    exact hc.deriv.deriv
  -- the integrand factor `f = u'' - κ² u` is continuous with compact support
  have hfcont : Continuous (fun s : ℝ => iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s) :=
    hcont2.sub (continuous_const.mul hu.continuous)
  have hfcs : HasCompactSupport (fun s : ℝ => iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s) := by
    have h1 : HasCompactSupport (fun s : ℝ => (κ : ℂ) ^ 2 * u s) :=
      HasCompactSupport.mul_left (f := fun _ : ℝ => (κ : ℂ) ^ 2) hc
    exact hcs2.sub h1
  -- bounded support of `u`
  obtain ⟨R, hRsub⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hR : ∀ x : ℝ, R < |x| → x ∉ tsupport u := by
    intro x hx hmem
    have h := hRsub hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h
    linarith
  -- vanishing of `u`, `u'`, `u''` off the support
  have hzero : ∀ x : ℝ, x ∉ tsupport u →
      u x = 0 ∧ deriv u x = 0 ∧ iteratedDeriv 2 u x = 0 := by
    intro x hx
    have h1 : u x = 0 := by
      by_contra hne
      exact hx (subset_tsupport u (Function.mem_support.mpr hne))
    have h2 : deriv u x = 0 := deriv_of_notMem_tsupport hx
    have hx' : x ∉ tsupport (deriv u) := fun h =>
      hx (closure_minimal support_deriv_subset (isClosed_tsupport u) h)
    have h3 : iteratedDeriv 2 u x = 0 := by
      rw [hI2]
      exact deriv_of_notMem_tsupport hx'
    exact ⟨h1, h2, h3⟩
  -- antiderivative `A = e^{κs} (u' - κ u)` of `e^{κs} f`
  have hdA : ∀ s : ℝ, HasDerivAt
      (fun y : ℝ => ((Real.exp (κ * y) : ℝ) : ℂ) * (deriv u y - (κ : ℂ) * u y))
      (((Real.exp (κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)) s := by
    intro s
    have h1 : HasDerivAt (fun y : ℝ => ((Real.exp (κ * y) : ℝ) : ℂ))
        ((Real.exp (κ * s) * (κ * 1) : ℝ) : ℂ) s :=
      (((hasDerivAt_id' s).const_mul κ).exp).ofReal_comp
    have h2 : HasDerivAt (fun y : ℝ => deriv u y - (κ : ℂ) * u y)
        (deriv (deriv u) s - (κ : ℂ) * deriv u s) s :=
      ((hdu s).hasDerivAt).sub (((hu1 s).hasDerivAt).const_mul (κ : ℂ))
    have h3 := h1.mul h2
    refine HasDerivAt.congr_deriv h3 ?_
    rw [hI2]
    push_cast
    ring
  -- antiderivative `B = e^{-κs} (u' + κ u)` of `e^{-κs} f`
  have hdB : ∀ s : ℝ, HasDerivAt
      (fun y : ℝ => ((Real.exp (-κ * y) : ℝ) : ℂ) * (deriv u y + (κ : ℂ) * u y))
      (((Real.exp (-κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)) s := by
    intro s
    have h1 : HasDerivAt (fun y : ℝ => ((Real.exp (-κ * y) : ℝ) : ℂ))
        ((Real.exp (-κ * s) * (-κ * 1) : ℝ) : ℂ) s :=
      (((hasDerivAt_id' s).const_mul (-κ)).exp).ofReal_comp
    have h2 : HasDerivAt (fun y : ℝ => deriv u y + (κ : ℂ) * u y)
        (deriv (deriv u) s + (κ : ℂ) * deriv u s) s :=
      ((hdu s).hasDerivAt).add (((hu1 s).hasDerivAt).const_mul (κ : ℂ))
    have h3 := h1.mul h2
    refine HasDerivAt.congr_deriv h3 ?_
    rw [hI2]
    push_cast
    ring
  -- `A` and `B` vanish eventually at `-∞` and `+∞`
  have hA_bot : Tendsto
      (fun y : ℝ => ((Real.exp (κ * y) : ℝ) : ℂ) * (deriv u y - (κ : ℂ) * u y)) atBot (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    rw [EventuallyEq, eventually_atBot]
    refine ⟨-(R + 1), fun b hb => ?_⟩
    obtain ⟨h1, h2, -⟩ :=
      hzero b (hR b (lt_of_lt_of_le (show R < -b by linarith) (neg_le_abs b)))
    simp [h1, h2]
  have hB_top : Tendsto
      (fun y : ℝ => ((Real.exp (-κ * y) : ℝ) : ℂ) * (deriv u y + (κ : ℂ) * u y)) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    rw [EventuallyEq, eventually_atTop]
    refine ⟨R + 1, fun b hb => ?_⟩
    obtain ⟨h1, h2, -⟩ :=
      hzero b (hR b (lt_of_lt_of_le (show R < b by linarith) (le_abs_self b)))
    simp [h1, h2]
  -- integrability of the two pieces
  have hEcont : Continuous (fun s : ℝ =>
      ((Real.exp (κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)) :=
    Continuous.mul (by fun_prop) hfcont
  have hEcs : HasCompactSupport (fun s : ℝ =>
      ((Real.exp (κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)) :=
    HasCompactSupport.mul_left (f := fun s : ℝ => ((Real.exp (κ * s) : ℝ) : ℂ)) hfcs
  have hEint : IntegrableOn (fun s : ℝ =>
      ((Real.exp (κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)) (Iic η) :=
    (Continuous.integrable_of_hasCompactSupport hEcont hEcs).integrableOn
  have hE'cont : Continuous (fun s : ℝ =>
      ((Real.exp (-κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)) :=
    Continuous.mul (by fun_prop) hfcont
  have hE'cs : HasCompactSupport (fun s : ℝ =>
      ((Real.exp (-κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)) :=
    HasCompactSupport.mul_left (f := fun s : ℝ => ((Real.exp (-κ * s) : ℝ) : ℂ)) hfcs
  have hEint' : IntegrableOn (fun s : ℝ =>
      ((Real.exp (-κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)) (Ioi η) :=
    (Continuous.integrable_of_hasCompactSupport hE'cont hE'cs).integrableOn
  have hgcont : Continuous (fun s : ℝ => ((-Real.exp (-κ * |η - s|) / (2 * κ) : ℝ) : ℂ) *
      (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)) :=
    Continuous.mul (by fun_prop) hfcont
  have hgcs : HasCompactSupport (fun s : ℝ => ((-Real.exp (-κ * |η - s|) / (2 * κ) : ℝ) : ℂ) *
      (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)) :=
    HasCompactSupport.mul_left (f := fun s : ℝ => ((-Real.exp (-κ * |η - s|) / (2 * κ) : ℝ) : ℂ))
      hfcs
  have hgint : Integrable (fun s : ℝ => ((-Real.exp (-κ * |η - s|) / (2 * κ) : ℝ) : ℂ) *
      (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)) :=
    Continuous.integrable_of_hasCompactSupport hgcont hgcs
  -- the piece on `s ≤ η`
  have hIic : ∫ s in Iic η, ((-Real.exp (-κ * |η - s|) / (2 * κ) : ℝ) : ℂ) *
      (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)
      = ((-Real.exp (-κ * η) / (2 * κ) : ℝ) : ℂ) *
        (((Real.exp (κ * η) : ℝ) : ℂ) * (deriv u η - (κ : ℂ) * u η)) := by
    have hcongr : ∫ s in Iic η, ((-Real.exp (-κ * |η - s|) / (2 * κ) : ℝ) : ℂ) *
        (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)
        = ∫ s in Iic η, ((-Real.exp (-κ * η) / (2 * κ) : ℝ) : ℂ) *
          (((Real.exp (κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro s hs
      have hs' : s ≤ η := hs
      show ((-Real.exp (-κ * |η - s|) / (2 * κ) : ℝ) : ℂ) *
          (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)
        = ((-Real.exp (-κ * η) / (2 * κ) : ℝ) : ℂ) *
          (((Real.exp (κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s))
      have e : Real.exp (-κ * |η - s|) = Real.exp (-κ * η) * Real.exp (κ * s) := by
        rw [← Real.exp_add, abs_of_nonneg (by linarith : (0 : ℝ) ≤ η - s)]
        congr 1
        ring
      rw [e]
      push_cast
      ring
    rw [hcongr, integral_const_mul]
    have hFTC : ∫ s in Iic η,
        ((Real.exp (κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)
        = ((Real.exp (κ * η) : ℝ) : ℂ) * (deriv u η - (κ : ℂ) * u η) - 0 :=
      integral_Iic_of_hasDerivAt_of_tendsto
        (f := fun y : ℝ => ((Real.exp (κ * y) : ℝ) : ℂ) * (deriv u y - (κ : ℂ) * u y))
        (f' := fun s : ℝ =>
          ((Real.exp (κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s))
        (m := 0)
        (hdA η).continuousAt.continuousWithinAt (fun x _ => hdA x) hEint hA_bot
    rw [hFTC, sub_zero]
  -- the piece on `s ≥ η`
  have hIoi : ∫ s in Ioi η, ((-Real.exp (-κ * |η - s|) / (2 * κ) : ℝ) : ℂ) *
      (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)
      = ((-Real.exp (κ * η) / (2 * κ) : ℝ) : ℂ) *
        (0 - ((Real.exp (-κ * η) : ℝ) : ℂ) * (deriv u η + (κ : ℂ) * u η)) := by
    have hcongr : ∫ s in Ioi η, ((-Real.exp (-κ * |η - s|) / (2 * κ) : ℝ) : ℂ) *
        (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)
        = ∫ s in Ioi η, ((-Real.exp (κ * η) / (2 * κ) : ℝ) : ℂ) *
          (((Real.exp (-κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      have hs' : η < s := hs
      show ((-Real.exp (-κ * |η - s|) / (2 * κ) : ℝ) : ℂ) *
          (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)
        = ((-Real.exp (κ * η) / (2 * κ) : ℝ) : ℂ) *
          (((Real.exp (-κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s))
      have e : Real.exp (-κ * |η - s|) = Real.exp (κ * η) * Real.exp (-κ * s) := by
        rw [← Real.exp_add, abs_of_nonpos (by linarith : η - s ≤ 0)]
        congr 1
        ring
      rw [e]
      push_cast
      ring
    rw [hcongr, integral_const_mul]
    have hFTC : ∫ s in Ioi η,
        ((Real.exp (-κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s)
        = 0 - ((Real.exp (-κ * η) : ℝ) : ℂ) * (deriv u η + (κ : ℂ) * u η) :=
      integral_Ioi_of_hasDerivAt_of_tendsto
        (f := fun y : ℝ => ((Real.exp (-κ * y) : ℝ) : ℂ) * (deriv u y + (κ : ℂ) * u y))
        (f' := fun s : ℝ =>
          ((Real.exp (-κ * s) : ℝ) : ℂ) * (iteratedDeriv 2 u s - (κ : ℂ) ^ 2 * u s))
        (m := 0)
        (hdB η).continuousAt.continuousWithinAt (fun x _ => hdB x) hEint' hB_top
    rw [hFTC]
  -- assemble
  have hsplit := integral_add_compl (μ := volume) (s := Iic η)
    (measurableSet_Iic : MeasurableSet (Iic η)) hgint
  rw [← hsplit, compl_Iic, hIic, hIoi]
  have hpqr : Real.exp (κ * η) * Real.exp (-κ * η) = 1 := by
    rw [← Real.exp_add, show κ * η + -κ * η = 0 by ring, Real.exp_zero]
  have hpq : ((Real.exp (κ * η) : ℝ) : ℂ) * ((Real.exp (-κ * η) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hpqr, Complex.ofReal_one]
  have hcast1 : ((-Real.exp (-κ * η) / (2 * κ) : ℝ) : ℂ)
      = -((Real.exp (-κ * η) : ℝ) : ℂ) / (2 * (κ : ℂ)) := by
    simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hcast2 : ((-Real.exp (κ * η) / (2 * κ) : ℝ) : ℂ)
      = -((Real.exp (κ * η) : ℝ) : ℂ) / (2 * (κ : ℂ)) := by
    simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [hcast1, hcast2]
  exact nzgk1_alg _ _ _ _ _ hκ0 hpq

/-- **Task `PartII-a:N02/4/5/1`: the one-dimensional Green identity** (the target `NzGreenKey1D`). -/
theorem nzGreenKey1D_proof : NzGreenKey1D := by
  unfold NzGreenKey1D
  intro k hk u hu hc η
  have hsub : ∫ t : ℝ, (nzGreen k t : ℂ) * (iteratedDeriv 2 u (η - t) - (k : ℂ) ^ 2 * u (η - t))
      = ∫ s : ℝ, (nzGreen k (η - s) : ℂ) * (iteratedDeriv 2 u s - (k : ℂ) ^ 2 * u s) := by
    have this := integral_sub_left_eq_self
      (fun t : ℝ => (nzGreen k t : ℂ) * (iteratedDeriv 2 u (η - t) - (k : ℂ) ^ 2 * u (η - t)))
      volume η
    simpa only [sub_sub_cancel] using this.symm
  have hk2 : ((|k| : ℝ) : ℂ) ^ 2 = (k : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
  have key := nzgk1_main |k| (abs_pos.mpr hk) u hu hc η
  rw [hsub]
  unfold nzGreen
  rw [← hk2]
  exact key

end UnforcedLeray.Short.PartIIa

end
