import UnforcedLeray.Lib.ComplexODEB.Neutral
import UnforcedLeray.Lib.ComplexODEB.Cauchy
import UnforcedLeray.Analysis.Rayleigh.RealSpeed.CriticalPoint
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# B0034 helper: exclusion of real limiting speeds on a log-annulus

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

Step of the continuation behind B0034 (`paper/main.tex`, lines 1012–1021; Lin 2003,
Lemma 5.8; whole-line analogue: the exclusion (3.10) of the Lin-free route, commit
4dd0a82). A `RealLimitMode a b β c U v` is what compactness produces from unstable
Dirichlet modes whose speeds tend to a real `c` and wavenumbers to `β`: `U' = v`,
`U(a) = U(b) = 0`, `∫ |U|² = 1`, and `v' = (β² + A/(Ω - c)) U` wherever `Ω ≠ c`.
It cannot exist when `1 < β < α` with `α` a neutral wavenumber of `[a, b]` and
`a < t_* < b` (`RealLimitMode.false`):

* `c = a_*`: the equation extends across `t_*` (`hasDerivAt_of_punctured`), so `U`
  is a neutral Dirichlet solution at `β`; it vanishes by `eq_zero_of_neutral_pair`.
* `c ≠ a_*`: at an interior critical point `t_c` the solution vanishes, since otherwise
  `v' ~ κ/(t - t_c)` is not integrable while `v` is bounded (`value_zero_at_critical`);
  then the ground state `h_c = e^t (Ω - c)` factorizes on both sides of `t_c`
  (`GroundState`) and `U = 0`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh UnforcedLeray.Rayleigh.Evans UnforcedLeray.Rayleigh.RealSpeed
open UnforcedLeray.Sturm UnforcedLeray.GaussianPotential

/-- The real limiting coefficient `β² + A/(Ω - c)`. -/
def realPotential (β c t : ℝ) : ℝ := β ^ 2 + gaussianRayleighCoefficient t / (neutralOmega t - c)

/-- A limit of normalized unstable Dirichlet modes at a real speed `c`. -/
structure RealLimitMode (a b β c : ℝ) (U v : ℝ → ℂ) : Prop where
  cont_v : Continuous v
  deriv_U : ∀ t, HasDerivAt U (v t) t
  left : U a = 0
  right : U b = 0
  mass : (∫ t in a..b, ‖U t‖ ^ 2) = 1
  ode : ∀ t ∈ Ioo a b, neutralOmega t ≠ c → HasDerivAt v ((realPotential β c t : ℂ) * U t) t

/-! ### The comparison profile `h_c` -/

/-- `h_c'`. -/
def speedDeriv (c t : ℝ) : ℝ := Real.exp t * ((1 - 2 * neutralRadius t) * neutralOmega t - c)

/-- `h_c''`. -/
def speedDeriv2 (c t : ℝ) : ℝ :=
  Real.exp t * ((1 - 8 * neutralRadius t + 4 * neutralRadius t ^ 2) * neutralOmega t - c)

theorem hasDerivAt_speedProfile' (c t : ℝ) :
    HasDerivAt (speedProfile c) (speedDeriv c t) t := hasDerivAt_speedProfile c t

theorem hasDerivAt_speedDeriv (c t : ℝ) : HasDerivAt (speedDeriv c) (speedDeriv2 c t) t := by
  have h := hasDerivAt_deriv_speedProfile c t
  have he : deriv (speedProfile c) = speedDeriv c := funext fun s => deriv_speedProfile c s
  rw [he] at h
  exact h

theorem continuous_speedProfile (c : ℝ) : Continuous (speedProfile c) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_speedProfile' c t).continuousAt

theorem continuous_speedDeriv (c : ℝ) : Continuous (speedDeriv c) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_speedDeriv c t).continuousAt

theorem speedProfile_ode' {c t : ℝ} (hc : neutralOmega t ≠ c) :
    speedDeriv2 c t = (1 + gaussianRayleighCoefficient t / (neutralOmega t - c)) *
      speedProfile c t := by
  have hd : neutralOmega t - c ≠ 0 := sub_ne_zero.mpr hc
  have hA := gaussianRayleighCoefficient_eq t
  unfold speedDeriv2 speedProfile
  rw [hA]
  field_simp
  ring

theorem speedDeriv_ne_zero {c t : ℝ} (hc : neutralOmega t = c) : speedDeriv c t ≠ 0 := by
  unfold speedDeriv
  rw [← hc]
  have h1 := Real.exp_pos t
  have h2 := neutralRadius_pos t
  have h3 := neutralOmega_pos t
  intro h
  have : Real.exp t * (-(2 * neutralRadius t * neutralOmega t)) = 0 := by linarith
  have h4 : 0 < Real.exp t * (2 * neutralRadius t * neutralOmega t) := by positivity
  linarith

/-- The bracket with `h_c` tends to zero at a zero of `f`. -/
theorem tendsto_speedBracket {c e : ℝ} {s : Set ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf'c : Continuous f') (he : f e = 0) :
    Tendsto (groundBracket f f' (speedProfile c) (speedDeriv c)) (𝓝[s \ {e}] e) (𝓝 0) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt
  by_cases hz : speedProfile c e = 0
  · have hΩ : neutralOmega e = c := (speedProfile_eq_zero_iff c e).mp hz
    have hle : 𝓝[s \ {e}] e ≤ 𝓝[s] e := nhdsWithin_mono _ sdiff_subset
    exact tendsto_groundBracket_of_simple_zero (hf e).hasDerivWithinAt
      hf'c.continuousAt.continuousWithinAt (hasDerivAt_speedProfile' c e).hasDerivWithinAt
      (continuous_speedDeriv c).continuousAt.continuousWithinAt he hz (speedDeriv_ne_zero hΩ)
  · exact tendsto_groundBracket_of_ne hfc.continuousAt.continuousWithinAt
      hf'c.continuousAt.continuousWithinAt
      (continuous_speedProfile c).continuousAt.continuousWithinAt
      (continuous_speedDeriv c).continuousAt.continuousWithinAt he hz

/-- On an interval without critical point inside, Dirichlet data force zero mass. -/
theorem integral_sq_zero_on {c β p q : ℝ} (hβ : 1 < β) (hpq : p < q) {f f' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf'c : Continuous f')
    (hfp : f p = 0) (hfq : f q = 0) (hne : ∀ t ∈ Ioo p q, neutralOmega t ≠ c)
    (hode : ∀ t ∈ Ioo p q, HasDerivAt f' (realPotential β c t * f t) t) :
    (∫ t in p..q, f t ^ 2) = 0 := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt
  have hl : Tendsto (groundBracket f f' (speedProfile c) (speedDeriv c)) (𝓝[>] p) (𝓝 0) := by
    have h := tendsto_speedBracket (c := c) (s := Ioi p) hf hf'c hfp
    rwa [sdiff_singleton_eq_self (by simp : p ∉ Ioi p)] at h
  have hr : Tendsto (groundBracket f f' (speedProfile c) (speedDeriv c)) (𝓝[<] q) (𝓝 0) := by
    have h := tendsto_speedBracket (c := c) (s := Iio q) hf hf'c hfq
    rwa [sdiff_singleton_eq_self (by simp : q ∉ Iio q)] at h
  exact integral_sq_eq_zero_of_groundBracket
    (Q := fun t => gaussianRayleighCoefficient t / (neutralOmega t - c)) hpq hβ
    hfc.continuousOn (fun t _ => hf t) hode
    (fun t _ => hasDerivAt_speedProfile' c t) (fun t _ => hasDerivAt_speedDeriv c t)
    (fun t ht => (speedProfile_ne_zero_iff c t).mpr (hne t ht))
    (fun t ht => speedProfile_ode' (hne t ht)) hl hr

/-! ### Extension of the equation across a point -/

/-- A derivative known off one point extends to that point when both sides are
continuous. -/
theorem hasDerivAt_of_punctured {v g : ℝ → ℝ} {p δ : ℝ} (hδ : 0 < δ)
    (hv : ContinuousAt v p) (hg : Continuous g)
    (hd : ∀ t ∈ Ioo (p - δ) (p + δ), t ≠ p → HasDerivAt v (g t) t) :
    HasDerivAt v (g p) p := by
  have hrep : ∀ t ∈ Ioo (p - δ) (p + δ), v t = v p + ∫ s in p..t, g s := by
    intro t ht
    rcases lt_trichotomy t p with htp | htp | htp
    · have hcont : ContinuousOn v (Icc t p) := by
        intro s hs
        rcases eq_or_lt_of_le hs.2 with hsp | hsp
        · rw [hsp]; exact hv.continuousWithinAt
        · exact (hd s ⟨by linarith [ht.1, hs.1], by linarith⟩ hsp.ne).continuousAt.continuousWithinAt
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htp.le hcont
        (fun s hs => hd s ⟨by linarith [ht.1, hs.1], by linarith [hs.2]⟩ hs.2.ne)
        (hg.intervalIntegrable t p)
      rw [intervalIntegral.integral_symm, h]
      ring
    · rw [htp]; simp
    · have hcont : ContinuousOn v (Icc p t) := by
        intro s hs
        rcases eq_or_lt_of_le hs.1 with hsp | hsp
        · rw [← hsp]; exact hv.continuousWithinAt
        · exact (hd s ⟨by linarith, by linarith [ht.2, hs.2]⟩ hsp.ne').continuousAt.continuousWithinAt
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htp.le hcont
        (fun s hs => hd s ⟨by linarith [hs.1], by linarith [ht.2, hs.2]⟩ hs.1.ne')
        (hg.intervalIntegrable p t)
      rw [h]
      ring
  have hderiv : HasDerivAt (fun t => v p + ∫ s in p..t, g s) (g p) p :=
    (hg.integral_hasStrictDerivAt p p).hasDerivAt.const_add (v p)
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (by linarith : p - δ < p) (by linarith : p < p + δ)] with t ht
  exact hrep t ht

/-! ### Vanishing at a nonneutral critical point -/

/-- A real limit vanishes at an interior critical point `Ω(t_c) = c ≠ a_*`. -/
theorem value_zero_at_critical {a b β c tc : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf'c : Continuous f')
    (htc : tc ∈ Ioo a b) (hΩ : neutralOmega tc = c) (hc : c ≠ gaussianCriticalSpeed)
    (hode : ∀ t ∈ Ioo a b, neutralOmega t ≠ c → HasDerivAt f' (realPotential β c t * f t) t) :
    f tc = 0 := by
  by_contra hne
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt
  have hA : gaussianRayleighCoefficient tc ≠ 0 := coefficient_ne_zero_at_critical hΩ hc
  have hd : offsetDeriv tc ≠ 0 := (offsetDeriv_neg tc).ne
  set κ : ℝ := gaussianRayleighCoefficient tc / offsetDeriv tc * f tc with hκ
  have hκ0 : κ ≠ 0 := mul_ne_zero (div_ne_zero hA hd) hne
  have hΩne : ∀ t, t ≠ tc → neutralOmega t ≠ c := fun t ht h =>
    ht (neutralOmega_injective (h.trans hΩ.symm))
  -- the limit of `w(τ) = V(τ) f(τ) (τ - t_c)`
  have hslope : Tendsto (slope neutralOmega tc) (𝓝[≠] tc) (𝓝 (offsetDeriv tc)) :=
    hasDerivAt_iff_tendsto_slope.mp (by
      have h := hasDerivAt_neutralOmega tc
      unfold offsetDeriv; exact h)
  have hle : 𝓝[>] tc ≤ 𝓝[≠] tc := nhdsWithin_mono _ (fun t ht => ne_of_gt ht)
  have hlin : Tendsto (fun τ : ℝ => τ - tc) (𝓝[>] tc) (𝓝 0) := by
    have : Tendsto (fun τ : ℝ => τ - tc) (𝓝 tc) (𝓝 (tc - tc)) := tendsto_id.sub_const tc
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hAc : Tendsto gaussianRayleighCoefficient (𝓝[>] tc) (𝓝 (gaussianRayleighCoefficient tc)) :=
    gaussianRayleighCoefficient_smooth.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hfl : Tendsto f (𝓝[>] tc) (𝓝 (f tc)) :=
    hfc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hw : Tendsto (fun τ => realPotential β c τ * f τ * (τ - tc)) (𝓝[>] tc) (𝓝 κ) := by
    have h1 : Tendsto (fun τ => (β ^ 2 * (τ - tc) + gaussianRayleighCoefficient τ /
        slope neutralOmega tc τ) * f τ) (𝓝[>] tc)
        (𝓝 ((β ^ 2 * 0 + gaussianRayleighCoefficient tc / offsetDeriv tc) * f tc)) :=
      (((hlin.const_mul _).add (hAc.div (hslope.mono_left hle) hd))).mul hfl
    rw [mul_zero, zero_add] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ' : τ - tc ≠ 0 := sub_ne_zero.mpr (ne_of_gt hτ)
    have hΩτ : neutralOmega τ - c ≠ 0 := sub_ne_zero.mpr (hΩne τ (ne_of_gt hτ))
    rw [slope_def_field, hΩ]
    unfold realPotential
    field_simp
  -- a right neighbourhood where `κ w ≥ κ²/2`
  have hev : ∀ᶠ τ in 𝓝[>] tc, |realPotential β c τ * f τ * (τ - tc) - κ| < |κ| / 2 := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hw).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < |κ| / 2))
    simpa [Real.norm_eq_abs] using this
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  set t₁ : ℝ := min ((tc + u) / 2) ((tc + b) / 2) with ht₁
  have ht₁c : tc < t₁ := lt_min (by linarith [hu.out]) (by linarith [htc.2])
  have ht₁u : t₁ < u := lt_of_le_of_lt (min_le_left _ _) (by linarith [hu.out])
  have ht₁b : t₁ < b := lt_of_le_of_lt (min_le_right _ _) (by linarith [htc.2])
  have hlow : ∀ τ ∈ Ioc tc t₁, κ ^ 2 / 2 ≤ κ * (realPotential β c τ * f τ * (τ - tc)) := by
    intro τ hτ
    have h := hsub ⟨hτ.1, hτ.2.trans_lt ht₁u⟩
    simp only [mem_setOf_eq] at h
    have h2 : |κ * (realPotential β c τ * f τ * (τ - tc) - κ)| ≤ |κ| * (|κ| / 2) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left h.le (abs_nonneg _)
    have h3 := neg_abs_le (κ * (realPotential β c τ * f τ * (τ - tc) - κ))
    have h4 : |κ| * |κ| = κ ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
    nlinarith
  -- the bound on `f'`
  obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf'c.continuousOn (s := Icc a b))
  have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hMf a (left_mem_Icc.mpr (htc.1.trans htc.2).le))
  -- monotonicity of `Φ = κ f' - (κ²/2) log(τ - t_c)` on `[s, t₁]`
  set T : ℝ := 4 * Mf / |κ| + 1 with hT
  set s : ℝ := tc + (t₁ - tc) * Real.exp (-T) with hs
  have hexp : Real.exp (-T) < 1 := Real.exp_lt_one_iff.mpr (by
    have : 0 ≤ 4 * Mf / |κ| := by positivity
    linarith)
  have hsc : tc < s := by
    have := Real.exp_pos (-T)
    have : 0 < (t₁ - tc) * Real.exp (-T) := mul_pos (by linarith) this
    linarith
  have hst : s < t₁ := by
    have h := mul_lt_mul_of_pos_left hexp (by linarith : (0 : ℝ) < t₁ - tc)
    linarith
  set Φ : ℝ → ℝ := fun τ => κ * f' τ - κ ^ 2 / 2 * Real.log (τ - tc) with hΦ
  have hΦd : ∀ τ ∈ Icc s t₁, HasDerivAt Φ
      (κ * (realPotential β c τ * f τ) - κ ^ 2 / 2 * (1 / (τ - tc))) τ := by
    intro τ hτ
    have hτc : tc < τ := hsc.trans_le hτ.1
    have hτab : τ ∈ Ioo a b := ⟨htc.1.trans hτc, hτ.2.trans_lt ht₁b⟩
    have h1 := (hode τ hτab (hΩne τ (ne_of_gt hτc))).const_mul κ
    have h2 := ((hasDerivAt_id τ).sub_const tc).log (sub_ne_zero.mpr (ne_of_gt hτc))
    have h3 := h1.sub (h2.const_mul (κ ^ 2 / 2))
    refine h3.congr_deriv ?_
    simp
  have hmono : MonotoneOn Φ (Icc s t₁) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc s t₁)
    · exact fun τ hτ => (hΦd τ hτ).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      exact fun τ hτ => (hΦd τ (Ioo_subset_Icc_self hτ)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro τ hτ
      rw [(hΦd τ (Ioo_subset_Icc_self hτ)).deriv]
      have hτc : tc < τ := hsc.trans hτ.1
      have hpos : 0 < τ - tc := sub_pos.mpr hτc
      have hl := hlow τ ⟨hτc, hτ.2.le⟩
      have : κ * (realPotential β c τ * f τ) = κ * (realPotential β c τ * f τ * (τ - tc)) /
          (τ - tc) := by field_simp
      rw [this, sub_nonneg, mul_one_div]
      exact div_le_div_of_nonneg_right hl hpos.le
  have hΦst := hmono ⟨le_rfl, hst.le⟩ ⟨hst.le, le_rfl⟩ hst.le
  simp only [hΦ] at hΦst
  have hlog : Real.log (t₁ - tc) - Real.log (s - tc) = T := by
    have h1 : s - tc = (t₁ - tc) * Real.exp (-T) := by rw [hs]; ring
    rw [h1, Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hb1 : |f' t₁| ≤ Mf := by
    have := hMf t₁ ⟨(htc.1.trans ht₁c).le, ht₁b.le⟩; rwa [Real.norm_eq_abs] at this
  have hb2 : |f' s| ≤ Mf := by
    have := hMf s ⟨(htc.1.trans hsc).le, (hst.trans ht₁b).le⟩; rwa [Real.norm_eq_abs] at this
  have hκf : κ * f' t₁ - κ * f' s ≤ 2 * |κ| * Mf := by
    have e1 : κ * f' t₁ ≤ |κ| * Mf := by
      calc κ * f' t₁ ≤ |κ * f' t₁| := le_abs_self _
        _ = |κ| * |f' t₁| := abs_mul _ _
        _ ≤ |κ| * Mf := mul_le_mul_of_nonneg_left hb1 (abs_nonneg _)
    have e2 : -(κ * f' s) ≤ |κ| * Mf := by
      calc -(κ * f' s) ≤ |κ * f' s| := neg_le_abs _
        _ = |κ| * |f' s| := abs_mul _ _
        _ ≤ |κ| * Mf := mul_le_mul_of_nonneg_left hb2 (abs_nonneg _)
    linarith
  have hκpos : 0 < |κ| := abs_pos.mpr hκ0
  have hTval : κ ^ 2 / 2 * T = 2 * |κ| * Mf + κ ^ 2 / 2 := by
    rw [hT]
    have : κ ^ 2 = |κ| * |κ| := by rw [← abs_mul, abs_mul_self, sq]
    rw [this]
    field_simp
    ring
  have : κ ^ 2 / 2 * (Real.log (t₁ - tc) - Real.log (s - tc)) ≤ κ * f' t₁ - κ * f' s := by
    linarith
  rw [hlog, hTval] at this
  have : 0 < κ ^ 2 / 2 := by positivity
  linarith

/-! ### The exclusion -/

/-- A real component of a real limiting mode has zero mass. -/
theorem real_component_integral_zero {a b α β c : ℝ} (hβ : β ∈ Ioo 1 α)
    (hcrit : neutralCriticalTime ∈ Ioo a b) (hα : neutralReal α a b = 0) {f f' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf'c : Continuous f') (hfa : f a = 0) (hfb : f b = 0)
    (hode : ∀ t ∈ Ioo a b, neutralOmega t ≠ c → HasDerivAt f' (realPotential β c t * f t) t) :
    (∫ t in a..b, f t ^ 2) = 0 := by
  have hab : a < b := hcrit.1.trans hcrit.2
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt
  by_cases hcs : c = gaussianCriticalSpeed
  · -- the neutral case
    subst hcs
    have hpot : ∀ t, t ≠ neutralCriticalTime →
        realPotential β gaussianCriticalSpeed t = β ^ 2 - Wlog t := by
      intro t ht
      have hJ : neutralOmega t - gaussianCriticalSpeed ≠ 0 := by
        have := gaussianOffset_ne_zero_off_critical ht
        unfold gaussianOffset at this; exact this
      unfold realPotential gaussianRayleighCoefficient gaussianOffset
      field_simp
      ring
    have hΩne : ∀ t, t ≠ neutralCriticalTime → neutralOmega t ≠ gaussianCriticalSpeed := by
      intro t ht h
      have := gaussianOffset_ne_zero_off_critical ht
      unfold gaussianOffset at this
      exact this (sub_eq_zero.mpr h)
    have hg : Continuous (fun t => (β ^ 2 - Wlog t) * f t) :=
      (continuous_const.sub continuous_Wlog).mul hfc
    have hode' : ∀ t ∈ Ioo a b, t ≠ neutralCriticalTime →
        HasDerivAt f' ((β ^ 2 - Wlog t) * f t) t := fun t ht htc => by
      rw [← hpot t htc]; exact hode t ht (hΩne t htc)
    obtain ⟨δ, hδ, hδsub⟩ : ∃ δ > 0, Ioo (neutralCriticalTime - δ) (neutralCriticalTime + δ) ⊆
        Ioo a b := by
      refine ⟨min (neutralCriticalTime - a) (b - neutralCriticalTime),
        lt_min (by linarith [hcrit.1]) (by linarith [hcrit.2]), fun t ht => ⟨?_, ?_⟩⟩
      · linarith [ht.1, min_le_left (neutralCriticalTime - a) (b - neutralCriticalTime)]
      · linarith [ht.2, min_le_right (neutralCriticalTime - a) (b - neutralCriticalTime)]
    have hcritd : HasDerivAt f' ((β ^ 2 - Wlog neutralCriticalTime) * f neutralCriticalTime)
        neutralCriticalTime :=
      hasDerivAt_of_punctured hδ hf'c.continuousAt hg
        (fun t ht htc => hode' t (hδsub ht) htc)
    have hall : ∀ t ∈ Ioo a b, HasDerivAt f' ((β ^ 2 - Wlog t) * f t) t := by
      intro t ht
      by_cases htc : t = neutralCriticalTime
      · rw [htc]; exact hcritd
      · exact hode' t ht htc
    have hzero := eq_zero_of_neutral_pair hβ.1 hβ.2 hcrit hα hfc.continuousOn hf'c.continuousOn
      (fun t _ => hf t) hall hfa hfb
    have : (∫ t in a..b, f t ^ 2) = ∫ t in a..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(volume : Measure ℝ).ae_ne b] with t htb hmem
      rw [uIoc_of_le hab.le] at hmem
      rw [hzero t ⟨hmem.1, lt_of_le_of_ne hmem.2 htb⟩]
      simp
    rw [this]; simp
  · -- a nonneutral real speed
    by_cases hex : ∃ tc ∈ Icc a b, neutralOmega tc = c
    · obtain ⟨tc, htc, hΩ⟩ := hex
      have hΩne : ∀ t, t ≠ tc → neutralOmega t ≠ c := fun t ht h =>
        ht (neutralOmega_injective (h.trans hΩ.symm))
      have hftc : f tc = 0 := by
        rcases eq_or_lt_of_le htc.1 with h | h
        · rw [← h]; exact hfa
        rcases eq_or_lt_of_le htc.2 with h' | h'
        · rw [h']; exact hfb
        exact value_zero_at_critical hf hf'c ⟨h, h'⟩ hΩ hcs hode
      have hleft : (∫ t in a..tc, f t ^ 2) = 0 := by
        rcases eq_or_lt_of_le htc.1 with h | h
        · rw [h]; simp
        exact integral_sq_zero_on hβ.1 h hf hf'c hfa hftc
          (fun t ht => hΩne t (ne_of_lt ht.2))
          (fun t ht => hode t ⟨ht.1, ht.2.trans_le htc.2⟩ (hΩne t (ne_of_lt ht.2)))
      have hright : (∫ t in tc..b, f t ^ 2) = 0 := by
        rcases eq_or_lt_of_le htc.2 with h | h
        · rw [h]; simp
        exact integral_sq_zero_on hβ.1 h hf hf'c hftc hfb
          (fun t ht => hΩne t (ne_of_gt ht.1))
          (fun t ht => hode t ⟨htc.1.trans_lt ht.1, ht.2⟩ (hΩne t (ne_of_gt ht.1)))
      have k1 : IntervalIntegrable (fun t => f t ^ 2) volume a tc := (hfc.pow 2).intervalIntegrable a tc
      have k2 : IntervalIntegrable (fun t => f t ^ 2) volume tc b := (hfc.pow 2).intervalIntegrable tc b
      rw [← intervalIntegral.integral_add_adjacent_intervals k1 k2, hleft, hright, add_zero]
    · push Not at hex
      exact integral_sq_zero_on hβ.1 hab hf hf'c hfa hfb
        (fun t ht => hex t (Ioo_subset_Icc_self ht))
        (fun t ht => hode t ht (hex t (Ioo_subset_Icc_self ht)))

/-- A real limiting mode cannot exist below a neutral wavenumber. -/
theorem RealLimitMode.false {a b α β c : ℝ} {U v : ℝ → ℂ} (h : RealLimitMode a b β c U v)
    (hβ : β ∈ Ioo 1 α) (hcrit : neutralCriticalTime ∈ Ioo a b) (hα : neutralReal α a b = 0) :
    False := by
  have hre := real_component_integral_zero (f := fun t => (U t).re) (f' := fun t => (v t).re)
    (c := c) hβ hcrit hα (fun t => hasDerivAt_re_comp (h.deriv_U t))
    (Complex.continuous_re.comp h.cont_v) (by simp [h.left]) (by simp [h.right])
    (fun t ht hne => by
      have := hasDerivAt_re_comp (h.ode t ht hne)
      rwa [Complex.re_ofReal_mul] at this)
  have him := real_component_integral_zero (f := fun t => (U t).im) (f' := fun t => (v t).im)
    (c := c) hβ hcrit hα (fun t => by
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (h.deriv_U t)
      exact this)
    (Complex.continuous_im.comp h.cont_v) (by simp [h.left]) (by simp [h.right])
    (fun t ht hne => by
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (h.ode t ht hne)
      have e : Complex.imCLM ((realPotential β c t : ℂ) * U t) =
          realPotential β c t * (U t).im := by
        simp [Complex.im_ofReal_mul]
      rw [e] at this
      exact this)
  have hUc : Continuous U := continuous_iff_continuousAt.mpr fun t => (h.deriv_U t).continuousAt
  have hsum : (∫ t in a..b, ‖U t‖ ^ 2) =
      (∫ t in a..b, (U t).re ^ 2) + ∫ t in a..b, (U t).im ^ 2 := by
    have k1 : IntervalIntegrable (fun t => (U t).re ^ 2) volume a b :=
      ((Complex.continuous_re.comp hUc).pow 2).intervalIntegrable a b
    have k2 : IntervalIntegrable (fun t => (U t).im ^ 2) volume a b :=
      ((Complex.continuous_im.comp hUc).pow 2).intervalIntegrable a b
    rw [← intervalIntegral.integral_add k1 k2]
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have := h.mass
  rw [hsum, hre, him] at this
  norm_num at this

end UnforcedLeray.ComplexODEB
