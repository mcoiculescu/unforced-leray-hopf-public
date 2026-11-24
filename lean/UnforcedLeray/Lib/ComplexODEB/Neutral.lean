import UnforcedLeray.Lib.ComplexODEB.GroundState
import UnforcedLeray.Lib.ComplexODE.NeutralSolution
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# B0034 helper: neutral Dirichlet modes on a log-annulus

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

Neutral part of the continuation behind B0034 (`paper/main.tex`, lines 990–1021;
blueprint units B0031–B0034). At the critical speed `c = a_*` the Rayleigh equation
becomes `F'' = (α² - W) F`; a neutral wavenumber of `[a,b]` is an `α` with a
Dirichlet solution, i.e. `neutralEvansFunction α a b = 0`.

* `neutralNormalizedF α a` is real (`neutralNormalizedF_eq_ofReal`), by uniqueness.
* A real Dirichlet solution at `γ > 1` with an interior zero vanishes: on the side
  of the zero not containing `t_* = neutralCriticalTime`, the ground state
  `h_* = e^t(Ω - a_*)` factorizes the form (`GroundState`), so the solution vanishes
  there, and uniqueness propagates (`neutral_dirichlet_eq_zero_or_ne`). This is the
  manuscript's "positivity of the `n = 1` form on functions vanishing at `t_*`".
* Hence a neutral normalized solution with `α > 1` is positive inside, in particular
  `F_α(t_*) ≠ 0` (`neutralReal_pos`), and two neutral wavenumbers above one cannot
  coexist (`eq_zero_of_neutral_pair`, Wronskian orthogonality).
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh UnforcedLeray.Rayleigh.Evans UnforcedLeray.Rayleigh.RealSpeed
open UnforcedLeray.Sturm UnforcedLeray.GaussianPotential NonUniqueEuler.LinODE

/-! ### Reality of the neutral normalized solution -/

theorem hasDerivAt_re_comp {G : ℝ → ℂ} {G' : ℂ} {t : ℝ} (h : HasDerivAt G G' t) :
    HasDerivAt (fun s => (G s).re) G'.re t := by
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  exact this

/-- Real part of the neutral normalized solution. -/
def neutralReal (α a t : ℝ) : ℝ := (neutralNormalizedF α a t).re

/-- Real part of its derivative. -/
def neutralRealDeriv (α a t : ℝ) : ℝ := (neutralNormalizedDerivative α a t).re

theorem neutralPotential_eq_ofReal (α t : ℝ) :
    neutralPotential α t = ((α ^ 2 - Wlog t : ℝ) : ℂ) := by
  simp [neutralPotential]

theorem hasDerivAt_neutralReal (α a t : ℝ) :
    HasDerivAt (neutralReal α a) (neutralRealDeriv α a t) t :=
  hasDerivAt_re_comp (hasDerivAt_neutralNormalizedF α a t)

theorem hasDerivAt_neutralRealDeriv (α a t : ℝ) :
    HasDerivAt (neutralRealDeriv α a) ((α ^ 2 - Wlog t) * neutralReal α a t) t := by
  have h := hasDerivAt_re_comp (hasDerivAt_neutralNormalizedDerivative α a t)
  rw [neutralPotential_eq_ofReal, Complex.re_ofReal_mul] at h
  exact h

@[simp] theorem neutralReal_initial (α a : ℝ) : neutralReal α a a = 0 := by
  simp [neutralReal]

@[simp] theorem neutralRealDeriv_initial (α a : ℝ) : neutralRealDeriv α a a = 1 := by
  simp [neutralRealDeriv]

theorem continuous_neutralReal (α a : ℝ) : Continuous (neutralReal α a) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_neutralReal α a t).continuousAt

theorem continuous_neutralRealDeriv (α a : ℝ) : Continuous (neutralRealDeriv α a) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_neutralRealDeriv α a t).continuousAt

/-- The neutral normalized solution is real. -/
theorem neutralNormalizedF_eq_ofReal (α a t : ℝ) :
    neutralNormalizedF α a t = (neutralReal α a t : ℂ) ∧
      neutralNormalizedDerivative α a t = (neutralRealDeriv α a t : ℂ) := by
  have hsol : IsSolOn (neutralPotential α) univ (fun s => (neutralReal α a s : ℂ))
      (fun s => (neutralRealDeriv α a s : ℂ)) := by
    refine ⟨fun s _ => (hasDerivAt_neutralReal α a s).ofReal_comp.hasDerivWithinAt,
      fun s _ => ?_⟩
    have h := (hasDerivAt_neutralRealDeriv α a s).ofReal_comp
    rw [neutralPotential_eq_ofReal]
    push_cast at h ⊢
    exact h.hasDerivWithinAt
  have huniq := IsSolOn.eqOn ordConnected_univ (continuous_neutralPotential α).continuousOn
    (neutralNormalizedPair_spec α a).1 hsol (mem_univ a)
    (by simp) (by simp)
  exact ⟨huniq.1 (mem_univ t), huniq.2 (mem_univ t)⟩

theorem neutralEvansFunction_eq_zero_iff (α a b : ℝ) :
    neutralEvansFunction α a b = 0 ↔ neutralReal α a b = 0 := by
  rw [neutralEvansFunction, (neutralNormalizedF_eq_ofReal α a b).1, Complex.ofReal_eq_zero]

/-! ### The ground state `h_*` -/

/-- `h_* = e^t (Ω - a_*)`. -/
def criticalProfile : ℝ → ℝ := speedProfile gaussianCriticalSpeed

/-- Its derivative. -/
def criticalProfileDeriv (t : ℝ) : ℝ :=
  Real.exp t * ((1 - 2 * neutralRadius t) * neutralOmega t - gaussianCriticalSpeed)

/-- Its second derivative. -/
def criticalProfileDeriv2 (t : ℝ) : ℝ :=
  Real.exp t * ((1 - 8 * neutralRadius t + 4 * neutralRadius t ^ 2) * neutralOmega t -
    gaussianCriticalSpeed)

theorem hasDerivAt_criticalProfile (t : ℝ) :
    HasDerivAt criticalProfile (criticalProfileDeriv t) t :=
  hasDerivAt_speedProfile _ t

theorem hasDerivAt_criticalProfileDeriv (t : ℝ) :
    HasDerivAt criticalProfileDeriv (criticalProfileDeriv2 t) t := by
  have h := hasDerivAt_deriv_speedProfile gaussianCriticalSpeed t
  have he : deriv (speedProfile gaussianCriticalSpeed) = criticalProfileDeriv := by
    funext s
    exact deriv_speedProfile _ s
  rw [he] at h
  exact h

theorem continuous_criticalProfile : Continuous criticalProfile :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_criticalProfile t).continuousAt

theorem continuous_criticalProfileDeriv : Continuous criticalProfileDeriv :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_criticalProfileDeriv t).continuousAt

theorem criticalProfile_ode (t : ℝ) :
    criticalProfileDeriv2 t = (1 + -Wlog t) * criticalProfile t := by
  have hA := gaussianRayleighCoefficient_eq t
  unfold gaussianRayleighCoefficient gaussianOffset at hA
  unfold criticalProfileDeriv2 criticalProfile speedProfile
  linear_combination (-Real.exp t) * hA

theorem criticalProfile_ne_zero {t : ℝ} (ht : t ≠ neutralCriticalTime) :
    criticalProfile t ≠ 0 := by
  have h := neutralProfile_ne_zero ht
  unfold neutralProfile at h
  unfold criticalProfile speedProfile gaussianCriticalSpeed
  exact h

theorem criticalProfile_at_critical : criticalProfile neutralCriticalTime = 0 := by
  unfold criticalProfile speedProfile gaussianCriticalSpeed
  simp

theorem criticalProfileDeriv_at_critical : criticalProfileDeriv neutralCriticalTime ≠ 0 := by
  unfold criticalProfileDeriv gaussianCriticalSpeed
  rw [neutralRadius_at_critical, neutralOmega_at_critical]
  have h1 := Real.exp_pos neutralCriticalTime
  have h2 := Real.exp_pos (-2)
  intro h
  nlinarith [mul_pos h1 h2]

/-! ### Dirichlet solutions of the neutral equation -/

section NeutralDirichlet

variable {a b γ : ℝ} {f f' : ℝ → ℝ}

/-- Bracket limit at an endpoint for the ground state `h_*`. -/
theorem tendsto_criticalBracket {s : Set ℝ} {e : ℝ}
    (hcrit : neutralCriticalTime ∈ Ioo a b) (hs : s ⊆ Icc a b) (he : e ∈ Icc a b)
    (hfc : ContinuousOn f (Icc a b)) (hf'c : ContinuousOn f' (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t) (hf0 : f e = 0) :
    Tendsto (groundBracket f f' criticalProfile criticalProfileDeriv) (𝓝[s \ {e}] e)
      (𝓝 0) := by
  by_cases hec : e = neutralCriticalTime
  · subst hec
    have hle : 𝓝[s \ {neutralCriticalTime}] neutralCriticalTime ≤ 𝓝[s] neutralCriticalTime :=
      nhdsWithin_mono _ sdiff_subset
    exact tendsto_groundBracket_of_simple_zero (hf _ hcrit).hasDerivWithinAt
      ((hf'c.continuousAt (Icc_mem_nhds hcrit.1 hcrit.2)).continuousWithinAt)
      (hasDerivAt_criticalProfile _).hasDerivWithinAt
      continuous_criticalProfileDeriv.continuousAt.continuousWithinAt hf0
      criticalProfile_at_critical criticalProfileDeriv_at_critical
  · have hsub : s \ {e} ⊆ Icc a b := sdiff_subset.trans hs
    exact tendsto_groundBracket_of_ne ((hfc e he).mono hsub) ((hf'c e he).mono hsub)
      continuous_criticalProfile.continuousAt.continuousWithinAt
      continuous_criticalProfileDeriv.continuousAt.continuousWithinAt hf0
      (criticalProfile_ne_zero hec)

/-- On a subinterval avoiding `t_*` in its interior, Dirichlet data force zero. -/
theorem neutral_side_eq_zero {p q : ℝ} (hγ : 1 < γ) (hpq : p < q) (hap : a ≤ p)
    (hqb : q ≤ b) (hcrit : neutralCriticalTime ∈ Ioo a b)
    (hcp : neutralCriticalTime ∉ Ioo p q)
    (hfc : ContinuousOn f (Icc a b)) (hf'c : ContinuousOn f' (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f' ((γ ^ 2 - Wlog t) * f t) t)
    (hp : f p = 0) (hq : f q = 0) :
    ∀ t ∈ Ioo p q, f t = 0 := by
  have hsub : Icc p q ⊆ Icc a b := Icc_subset_Icc hap hqb
  have hsubo : Ioo p q ⊆ Ioo a b := Ioo_subset_Ioo hap hqb
  have hne : ∀ t ∈ Ioo p q, criticalProfile t ≠ 0 := fun t ht =>
    criticalProfile_ne_zero (fun h => hcp (h ▸ ht))
  have hl : Tendsto (groundBracket f f' criticalProfile criticalProfileDeriv) (𝓝[>] p)
      (𝓝 0) := by
    refine (tendsto_criticalBracket hcrit hsub (hsub (left_mem_Icc.mpr hpq.le)) hfc hf'c hf
      hp).mono_left (nhdsWithin_le_of_mem ?_)
    filter_upwards [Ioo_mem_nhdsGT hpq] with t ht
    exact ⟨Ioo_subset_Icc_self ht, ne_of_gt ht.1⟩
  have hr : Tendsto (groundBracket f f' criticalProfile criticalProfileDeriv) (𝓝[<] q)
      (𝓝 0) := by
    refine (tendsto_criticalBracket hcrit hsub (hsub (right_mem_Icc.mpr hpq.le)) hfc hf'c hf
      hq).mono_left (nhdsWithin_le_of_mem ?_)
    filter_upwards [Ioo_mem_nhdsLT hpq] with t ht
    exact ⟨Ioo_subset_Icc_self ht, ne_of_lt ht.2⟩
  have hint := integral_sq_eq_zero_of_groundBracket (Q := fun t => -Wlog t) hpq hγ
    (hfc.mono hsub) (fun t ht => hf t (hsubo ht))
    (fun t ht => by
      have h := hf' t (hsubo ht)
      rw [sub_eq_add_neg] at h
      exact h)
    (fun t _ => hasDerivAt_criticalProfile t) (fun t _ => hasDerivAt_criticalProfileDeriv t)
    hne (fun t _ => criticalProfile_ode t) hl hr
  exact eq_zero_of_integral_sq_eq_zero (hfc.mono hsub) hint

/-- A real Dirichlet solution of the neutral equation at `γ > 1` either vanishes or
has no interior zero. -/
theorem neutral_dirichlet_eq_zero_or_ne (hγ : 1 < γ)
    (hcrit : neutralCriticalTime ∈ Ioo a b)
    (hfc : ContinuousOn f (Icc a b)) (hf'c : ContinuousOn f' (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f' ((γ ^ 2 - Wlog t) * f t) t)
    (hfa : f a = 0) (hfb : f b = 0) :
    (∀ t ∈ Ioo a b, f t = 0) ∨ (∀ t ∈ Ioo a b, f t ≠ 0) := by
  by_cases hz : ∃ τ ∈ Ioo a b, f τ = 0
  · left
    obtain ⟨τ, hτ, hfτ⟩ := hz
    -- vanishing on one side of τ
    have hside : ∃ p q, p < q ∧ Ioo p q ⊆ Ioo a b ∧ ∀ t ∈ Ioo p q, f t = 0 := by
      rcases le_or_gt τ neutralCriticalTime with hle | hlt
      · refine ⟨a, τ, hτ.1, Ioo_subset_Ioo le_rfl hτ.2.le, ?_⟩
        exact neutral_side_eq_zero hγ hτ.1 le_rfl hτ.2.le hcrit
          (fun h => (not_lt.mpr hle) h.2) hfc hf'c hf hf' hfa hfτ
      · refine ⟨τ, b, hτ.2, Ioo_subset_Ioo hτ.1.le le_rfl, ?_⟩
        exact neutral_side_eq_zero hγ hτ.2 hτ.1.le le_rfl hcrit
          (fun h => (not_lt.mpr h.1.le) hlt) hfc hf'c hf hf' hfτ hfb
    obtain ⟨p, q, hpq, hsub, hzero⟩ := hside
    set s₀ : ℝ := (p + q) / 2 with hs₀
    have hs₀m : s₀ ∈ Ioo p q := ⟨by linarith, by linarith⟩
    have hloc : f =ᶠ[𝓝 s₀] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds hs₀m.1 hs₀m.2] with t ht
      exact hzero t ht
    have hd0 : f' s₀ = 0 :=
      (hf s₀ (hsub hs₀m)).unique ((hasDerivAt_const s₀ (0 : ℝ)).congr_of_eventuallyEq hloc)
    -- uniqueness for the complexified equation
    have hsol : IsSolOn (fun t => ((γ ^ 2 - Wlog t : ℝ) : ℂ)) (Ioo a b)
        (fun t => (f t : ℂ)) (fun t => (f' t : ℂ)) := by
      refine ⟨fun t ht => (hf t ht).ofReal_comp.hasDerivWithinAt, fun t ht => ?_⟩
      have h := (hf' t ht).ofReal_comp
      push_cast at h ⊢
      exact h.hasDerivWithinAt
    have hcV : ContinuousOn (fun t => ((γ ^ 2 - Wlog t : ℝ) : ℂ)) (Ioo a b) :=
      (Complex.continuous_ofReal.comp (continuous_const.sub continuous_Wlog)).continuousOn
    have hz := IsSolOn.eqOn_zero ordConnected_Ioo hcV hsol (hsub hs₀m)
      (by simp [hzero s₀ hs₀m]) (by simp [hd0])
    intro t ht
    have := hz.1 ht
    simpa using this
  · right
    push Not at hz
    exact hz

end NeutralDirichlet

/-! ### Positivity of neutral normalized solutions -/

/-- A function with derivative one at `a` and value zero is positive just right of `a`. -/
theorem eventually_pos_of_hasDerivAt_one {g : ℝ → ℝ} {a : ℝ} (hg : HasDerivAt g 1 a)
    (h0 : g a = 0) : ∀ᶠ t in 𝓝[>] a, 0 < g t := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hg
  have hev : ∀ᶠ t in 𝓝[≠] a, 0 < slope g a t := hs.eventually (lt_mem_nhds one_pos)
  have hle : 𝓝[>] a ≤ 𝓝[≠] a := nhdsWithin_mono _ (fun t ht => ne_of_gt ht)
  filter_upwards [hev.filter_mono hle, self_mem_nhdsWithin] with t ht hta
  rw [slope_def_field, h0, sub_zero] at ht
  have hpos : 0 < t - a := sub_pos.mpr hta
  exact (div_pos_iff_of_pos_right hpos).mp ht

/-- A continuous function without zeros on an open interval has a constant sign. -/
theorem pos_or_neg_of_ne_zero {a b : ℝ} {f : ℝ → ℝ} (hfc : ContinuousOn f (Ioo a b))
    (hne : ∀ t ∈ Ioo a b, f t ≠ 0) :
    (∀ t ∈ Ioo a b, 0 < f t) ∨ (∀ t ∈ Ioo a b, f t < 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨s, hs, hfs⟩, ⟨t, ht, hft⟩⟩ := hcon
  have hfs' : f s < 0 := lt_of_le_of_ne hfs (hne s hs)
  have hft' : 0 < f t := lt_of_le_of_ne hft (hne t ht).symm
  have hsub : uIcc s t ⊆ Ioo a b := ordConnected_Ioo.uIcc_subset hs ht
  have hivt := intermediate_value_uIcc (hfc.mono hsub)
  have h0 : (0 : ℝ) ∈ uIcc (f s) (f t) := by
    rw [mem_uIcc]
    left
    exact ⟨hfs'.le, hft'.le⟩
  obtain ⟨x, hx, hfx⟩ := hivt h0
  exact hne x (hsub hx) hfx

/-- A neutral normalized solution with `α > 1` that vanishes at `b` is positive inside;
in particular it does not vanish at the critical layer. -/
theorem neutralReal_pos {α a b : ℝ} (hα : 1 < α) (hcrit : neutralCriticalTime ∈ Ioo a b)
    (hb : neutralReal α a b = 0) : ∀ t ∈ Ioo a b, 0 < neutralReal α a t := by
  have hab : a < b := hcrit.1.trans hcrit.2
  have hpos := eventually_pos_of_hasDerivAt_one
    (by simpa using hasDerivAt_neutralReal α a a) (neutralReal_initial α a)
  have hcases := neutral_dirichlet_eq_zero_or_ne hα hcrit
    (continuous_neutralReal α a).continuousOn (continuous_neutralRealDeriv α a).continuousOn
    (fun t _ => hasDerivAt_neutralReal α a t) (fun t _ => hasDerivAt_neutralRealDeriv α a t)
    (neutralReal_initial α a) hb
  obtain ⟨t₀, ht₀, ht₀b⟩ : ∃ t₀, 0 < neutralReal α a t₀ ∧ t₀ ∈ Ioo a b := by
    obtain ⟨t₀, ht₀⟩ := (hpos.and (Ioo_mem_nhdsGT hab)).exists
    exact ⟨t₀, ht₀⟩
  rcases hcases with hzero | hne
  · exact absurd (hzero t₀ ht₀b) ht₀.ne'
  · rcases pos_or_neg_of_ne_zero (continuous_neutralReal α a).continuousOn hne with h | h
    · exact h
    · exact absurd (h t₀ ht₀b) (not_lt.mpr ht₀.le)

theorem neutralReal_critical_ne_zero {α a b : ℝ} (hα : 1 < α)
    (hcrit : neutralCriticalTime ∈ Ioo a b) (hb : neutralReal α a b = 0) :
    neutralReal α a neutralCriticalTime ≠ 0 :=
  (neutralReal_pos hα hcrit hb _ hcrit).ne'

/-! ### Orthogonality and uniqueness of the neutral wavenumber -/

/-- Wronskian orthogonality of a Dirichlet solution at `γ` and the neutral normalized
solution at `α`. -/
theorem integral_mul_neutralReal_eq_zero {a b γ α : ℝ} (hab : a ≤ b) {f f' : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc a b)) (hf'c : ContinuousOn f' (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f' ((γ ^ 2 - Wlog t) * f t) t)
    (hfa : f a = 0) (hfb : f b = 0) (hb : neutralReal α a b = 0) :
    (γ ^ 2 - α ^ 2) * (∫ t in a..b, f t * neutralReal α a t) = 0 := by
  set g := neutralReal α a
  set g' := neutralRealDeriv α a
  have hw : ∀ t ∈ Ioo a b, HasDerivAt (fun s => f' s * g s - f s * g' s)
      ((γ ^ 2 - α ^ 2) * (f t * g t)) t := by
    intro t ht
    have h := ((hf' t ht).mul (hasDerivAt_neutralReal α a t)).sub
      ((hf t ht).mul (hasDerivAt_neutralRealDeriv α a t))
    refine h.congr_deriv ?_
    ring
  have hwc : ContinuousOn (fun s => f' s * g s - f s * g' s) (Icc a b) :=
    (hf'c.mul (continuous_neutralReal α a).continuousOn).sub
      (hfc.mul (continuous_neutralRealDeriv α a).continuousOn)
  have hint : IntervalIntegrable (fun t => (γ ^ 2 - α ^ 2) * (f t * g t)) volume a b :=
    (continuousOn_const.mul (hfc.mul (continuous_neutralReal α a).continuousOn)
      ).intervalIntegrable_of_Icc hab
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hwc hw hint
  rw [intervalIntegral.integral_const_mul] at key
  have hga : g a = 0 := neutralReal_initial α a
  rw [key, hfa, hfb, hb, hga]
  ring

/-- A real Dirichlet solution of the neutral equation at `γ ∈ (1, α)`, where `α` is a
neutral wavenumber, vanishes: the neutral wavenumber above one is unique. -/
theorem eq_zero_of_neutral_pair {a b γ α : ℝ} (hγ : 1 < γ) (hγα : γ < α)
    (hcrit : neutralCriticalTime ∈ Ioo a b) (hb : neutralReal α a b = 0) {f f' : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc a b)) (hf'c : ContinuousOn f' (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f' ((γ ^ 2 - Wlog t) * f t) t)
    (hfa : f a = 0) (hfb : f b = 0) : ∀ t ∈ Ioo a b, f t = 0 := by
  have hab : a < b := hcrit.1.trans hcrit.2
  have hα : 1 < α := hγ.trans hγα
  have hgpos := neutralReal_pos hα hcrit hb
  have horth := integral_mul_neutralReal_eq_zero hab.le hfc hf'c hf hf' hfa hfb hb
  have hne : γ ^ 2 - α ^ 2 ≠ 0 := by nlinarith
  have horth' : (∫ t in a..b, f t * neutralReal α a t) = 0 :=
    (mul_eq_zero.mp horth).resolve_left hne
  rcases neutral_dirichlet_eq_zero_or_ne hγ hcrit hfc hf'c hf hf' hfa hfb with h | h
  · exact h
  · exfalso
    have hint : IntervalIntegrable (fun t => f t * neutralReal α a t) volume a b :=
      (hfc.mul (continuous_neutralReal α a).continuousOn).intervalIntegrable_of_Icc hab.le
    rcases pos_or_neg_of_ne_zero (hfc.mono Ioo_subset_Icc_self) h with hp | hn
    · have := intervalIntegral.intervalIntegral_pos_of_pos_on hint
        (fun t ht => mul_pos (hp t ht) (hgpos t ht)) hab
      linarith
    · have := intervalIntegral.intervalIntegral_pos_of_pos_on
        (f := fun t => -(f t * neutralReal α a t)) hint.neg
        (fun t ht => by
          have := mul_pos (neg_pos.mpr (hn t ht)) (hgpos t ht)
          simpa [neg_mul] using this) hab
      rw [intervalIntegral.integral_neg] at this
      linarith

end UnforcedLeray.ComplexODEB
