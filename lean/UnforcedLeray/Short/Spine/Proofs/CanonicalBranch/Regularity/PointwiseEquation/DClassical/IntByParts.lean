import UnforcedLeray.Short.Spine.Sub.SP_CAN4_5
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation.DClassical.WeightedFund

/-!
# Weighted integration by parts for `oscillatorD` (helper for `DClassicalAe`)

With the `X_G` weight `w r = 4π e^{r²/4} r` (`DClassicalAux.wDens`, complex copy `wC`), the
classical oscillator satisfies, for `r ≠ 0`,
`oscillatorD f r * w r = (w r * f'' r + w' r * f' r) + (-4/r² + 2) * w r * f r`, where
`w' r = 4π e^{r²/4} (r²/2 + 1)`. Hence for `ψ` smooth and vanishing near `(-∞, a)` and `(b, ∞)`,
`∫ (oscillatorD ψ) g w = ∫ ψ (oscillatorD g) w` for every `g` smooth on `(0, ∞)`:
two integrations by parts on `[a/2, b+1] ⊂ (0, ∞)`, no boundary terms.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter intervalIntegral
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine.DClassicalAux

open UnforcedLeray.Blueprint.Planar

/-- The `X_G` weight `4π e^{r²/4} r` as a complex function. -/
def wC (r : ℝ) : ℂ := (wDens r : ℂ)

/-- Its derivative `d/dr (4π e^{r²/4} r) = 4π e^{r²/4} (r²/2 + 1)`. -/
def wC' (r : ℝ) : ℂ := ((4 * Real.pi * Real.exp (r ^ 2 / 4) * (r ^ 2 / 2 + 1) : ℝ) : ℂ)

theorem hasDerivAt_wC (r : ℝ) : HasDerivAt wC (wC' r) r := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 / 4) (r / 2) r :=
    ((hasDerivAt_pow 2 r).div_const 4).congr_deriv (by norm_num <;> ring)
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (s ^ 2 / 4))
      (Real.exp (r ^ 2 / 4) * (r / 2)) r := h1.exp
  have h3 : HasDerivAt (fun s : ℝ => 4 * Real.pi * Real.exp (s ^ 2 / 4) * s)
      (4 * Real.pi * (Real.exp (r ^ 2 / 4) * (r / 2)) * r +
        4 * Real.pi * Real.exp (r ^ 2 / 4) * 1) r :=
    (h2.const_mul (4 * Real.pi)).mul (hasDerivAt_id' r)
  have h4 := h3.ofReal_comp
  convert h4 using 1
  · unfold wC wDens
    rfl
  · unfold wC'
    push_cast
    ring

/-- Continuity of the complex weight derivative. -/
theorem continuous_wC' : Continuous wC' := by
  unfold wC'
  fun_prop

theorem continuous_wC : Continuous wC :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_wC x).continuousAt

/-- **Pointwise identity.** For `r ≠ 0`, `oscillatorD f r · w r` splits into the weighted
second-order part and a zeroth-order part. -/
theorem oscillatorD_mul_wC (f : ℝ → ℂ) {r : ℝ} (hr : r ≠ 0) :
    oscillatorD f r * wC r = wC' r * deriv f r + wC r * deriv (deriv f) r +
      (-4 / (r : ℂ) ^ 2 + 2) * wC r * f r := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  unfold oscillatorD wC wC' wDens
  push_cast
  field_simp
  ring

/-- If `ψ` vanishes near `r`, then `oscillatorD ψ r = 0`. -/
theorem oscillatorD_eq_zero_of_eventually {ψ : ℝ → ℂ} {r : ℝ}
    (h : ψ =ᶠ[𝓝 r] fun _ => 0) : oscillatorD ψ r = 0 := by
  have h0 : ψ r = 0 := h.eq_of_nhds
  have h1 : deriv ψ r = 0 := by
    rw [h.deriv_eq]
    simp
  have h2 : deriv (deriv ψ) r = 0 := by
    rw [h.deriv.deriv_eq]
    simp
  unfold oscillatorD
  rw [h0, h1, h2]
  ring

/-- **Integration by parts on a compact interval.** Boundary terms vanish because `ψ` and
`ψ'` vanish at the endpoints. -/
theorem interval_ibp {ψ g : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    {P Q : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hψP : ψ P = 0) (hψQ : ψ Q = 0)
    (hdP : deriv ψ P = 0) (hdQ : deriv ψ Q = 0) :
    ∫ r in P..Q, oscillatorD ψ r * g r * wC r = ∫ r in P..Q, ψ r * oscillatorD g r * wC r := by
  have hsub : uIcc P Q ⊆ Ioi 0 := by
    intro x hx
    rw [uIcc_of_le hPQ] at hx
    exact lt_of_lt_of_le hP hx.1
  -- derivatives of `ψ` (global)
  have hdψ1 : ∀ x, HasDerivAt ψ (deriv ψ x) x := fun x =>
    ((hψ.differentiable (by simp)) x).hasDerivAt
  have hψd : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hdψ2 : ∀ x, HasDerivAt (deriv ψ) (deriv (deriv ψ) x) x := fun x =>
    ((hψd.differentiable (by simp)) x).hasDerivAt
  have hcψ : Continuous ψ := hψ.continuous
  have hcdψ : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hcddψ : Continuous (deriv (deriv ψ)) := hψd.continuous_deriv (by simp)
  -- derivatives of `g` (on `(0, ∞)`)
  have hg1 : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (deriv g x) x := fun x hx =>
    ((hg.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have hdg : ContDiffOn ℝ ∞ (deriv g) (Ioi 0) := hg.deriv_of_isOpen isOpen_Ioi (by simp)
  have hg2 : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (deriv g) (deriv (deriv g) x) x := fun x hx =>
    ((hdg.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have hcg : ContinuousOn g (uIcc P Q) := hg.continuousOn.mono hsub
  have hcdg : ContinuousOn (deriv g) (uIcc P Q) := hdg.continuousOn.mono hsub
  have hcddg : ContinuousOn (deriv (deriv g)) (uIcc P Q) :=
    (hdg.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).mono hsub
  have hcwC := continuous_wC
  have hcwC' := continuous_wC'
  -- the derivative functions in the two integrations by parts
  set v1 : ℝ → ℂ := fun x => wC x * deriv ψ x with hv1def
  set v1' : ℝ → ℂ := fun x => wC' x * deriv ψ x + wC x * deriv (deriv ψ) x with hv1'def
  set Γ : ℝ → ℂ := fun x => wC x * deriv g x with hΓdef
  set Γ' : ℝ → ℂ := fun x => wC' x * deriv g x + wC x * deriv (deriv g) x with hΓ'def
  have hcv1' : ContinuousOn v1' (uIcc P Q) :=
    ((hcwC'.mul hcdψ).add (hcwC.mul hcddψ)).continuousOn
  have hcΓ' : ContinuousOn Γ' (uIcc P Q) :=
    ((hcwC'.continuousOn.mul hcdg).add (hcwC.continuousOn.mul hcddg))
  -- Step A: `∫ g v1' = - ∫ g' v1`
  have hA := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := P) (b := Q)
    (u := g) (v := v1) (u' := deriv g) (v' := v1')
    (fun x hx => hg1 x (hsub hx)) (fun x _ => (hasDerivAt_wC x).mul (hdψ2 x))
    hcdg.intervalIntegrable hcv1'.intervalIntegrable
  have hv1P : v1 P = 0 := by simp [v1, hdP]
  have hv1Q : v1 Q = 0 := by simp [v1, hdQ]
  -- Step B: `∫ g' v1 = ∫ ψ' Γ`
  have hB : ∫ x in P..Q, deriv g x * v1 x = ∫ x in P..Q, deriv ψ x * Γ x :=
    intervalIntegral.integral_congr (fun x _ => by simp only [v1, Γ]; ring)
  -- Step C: `∫ ψ Γ' = - ∫ ψ' Γ`
  have hC := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := P) (b := Q)
    (u := ψ) (v := Γ) (u' := deriv ψ) (v' := Γ')
    (fun x _ => hdψ1 x) (fun x hx => (hasDerivAt_wC x).mul (hg2 x (hsub hx)))
    hcdψ.continuousOn.intervalIntegrable hcΓ'.intervalIntegrable
  have hkey : ∫ x in P..Q, g x * v1' x = ∫ x in P..Q, ψ x * Γ' x := by
    rw [hA, hB, hC, hv1P, hv1Q, hψP, hψQ]
    ring
  -- Continuity of the remaining integrands on `[P, Q]`
  have hcV : ContinuousOn (fun x : ℝ => (-4 / (x : ℂ) ^ 2 + 2) * wC x) (uIcc P Q) := by
    apply ContinuousOn.mul _ hcwC.continuousOn
    apply ContinuousOn.add _ continuousOn_const
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hsub hx).ne'
    exact pow_ne_zero 2 hx0
  have hint1 : IntervalIntegrable (fun r => g r * v1' r) volume P Q :=
    (hcg.mul hcv1').intervalIntegrable
  have hint2 : IntervalIntegrable (fun r => ψ r * ((-4 / (r : ℂ) ^ 2 + 2) * wC r * g r))
      volume P Q :=
    (hcψ.continuousOn.mul (hcV.mul hcg)).intervalIntegrable
  have hint3 : IntervalIntegrable (fun r => ψ r * Γ' r) volume P Q :=
    (hcψ.continuousOn.mul hcΓ').intervalIntegrable
  -- Step D: pointwise rewriting of both integrands
  have hL : ∫ r in P..Q, oscillatorD ψ r * g r * wC r =
      ∫ r in P..Q, (g r * v1' r + ψ r * ((-4 / (r : ℂ) ^ 2 + 2) * wC r * g r)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : x ≠ 0 := (hsub hx).ne'
    simp only [v1']
    have e := oscillatorD_mul_wC ψ hx0
    calc oscillatorD ψ x * g x * wC x = (oscillatorD ψ x * wC x) * g x := by ring
      _ = _ := by rw [e]; ring
  have hR : ∫ r in P..Q, ψ r * oscillatorD g r * wC r =
      ∫ r in P..Q, (ψ r * Γ' r + ψ r * ((-4 / (r : ℂ) ^ 2 + 2) * wC r * g r)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : x ≠ 0 := (hsub hx).ne'
    simp only [Γ']
    have e := oscillatorD_mul_wC g hx0
    calc ψ x * oscillatorD g x * wC x = ψ x * (oscillatorD g x * wC x) := by ring
      _ = _ := by rw [e]; ring
  rw [hL, hR, intervalIntegral.integral_add hint1 hint2,
    intervalIntegral.integral_add hint3 hint2, hkey]

/-- **Weighted integration by parts on `(0, ∞)`.** For `ψ` smooth, vanishing on `(-∞, a)` and on
`(b, ∞)` with `0 < a`, and `g` smooth on `(0, ∞)`:
`∫ oscillatorD ψ · g · w = ∫ ψ · oscillatorD g · w` (integrals over `ℝ`). -/
theorem oscillatorD_ibp {ψ g : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hψa : ∀ r, r < a → ψ r = 0)
    (hψb : ∀ r, b < r → ψ r = 0) :
    ∫ r, oscillatorD ψ r * g r * wC r = ∫ r, ψ r * oscillatorD g r * wC r := by
  have hP : (0 : ℝ) < a / 2 := by linarith
  have hPQ : a / 2 ≤ b + 1 := by linarith
  have hPa : a / 2 < a := by linarith
  have hQb : b < b + 1 := by linarith
  have hzeroL : ∀ r, r < a → ψ =ᶠ[𝓝 r] fun _ => 0 := fun r hr =>
    Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hr) (fun x hx => hψa x hx)
  have hzeroR : ∀ r, b < r → ψ =ᶠ[𝓝 r] fun _ => 0 := fun r hr =>
    Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hr) (fun x hx => hψb x hx)
  have hψP0 : ψ (a / 2) = 0 := hψa _ hPa
  have hψQ0 : ψ (b + 1) = 0 := hψb _ hQb
  have hdP : deriv ψ (a / 2) = 0 := by
    rw [(hzeroL _ hPa).deriv_eq]
    simp
  have hdQ : deriv ψ (b + 1) = 0 := by
    rw [(hzeroR _ hQb).deriv_eq]
    simp
  have hint := interval_ibp hψ hg hP hPQ hψP0 hψQ0 hdP hdQ
  have hL0 : ∀ r, r ∉ Icc (a / 2) (b + 1) → oscillatorD ψ r * g r * wC r = 0 := by
    intro r hr
    rw [mem_Icc, not_and_or, not_le, not_le] at hr
    rcases hr with h | h
    · rw [oscillatorD_eq_zero_of_eventually (hzeroL r (by linarith))]
      ring
    · rw [oscillatorD_eq_zero_of_eventually (hzeroR r (by linarith))]
      ring
  have hR0 : ∀ r, r ∉ Icc (a / 2) (b + 1) → ψ r * oscillatorD g r * wC r = 0 := by
    intro r hr
    rw [mem_Icc, not_and_or, not_le, not_le] at hr
    rcases hr with h | h
    · rw [hψa r (by linarith)]
      ring
    · rw [hψb r (by linarith)]
      ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (f := fun r => oscillatorD ψ r * g r * wC r) hL0,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (f := fun r => ψ r * oscillatorD g r * wC r) hR0,
    integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hPQ, ← intervalIntegral.integral_of_le hPQ]
  exact hint

end UnforcedLeray.Short.Spine.DClassicalAux
