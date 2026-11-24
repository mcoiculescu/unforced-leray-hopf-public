import UnforcedLeray.Lib.ComplexODEB.Neutral
import UnforcedLeray.GaussianCompactTrial
import UnforcedLeray.Analysis.Sturm.NeutralFactorizationBasic
import NonUniqueEuler.P.Infra.ODE.Param
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# B0034 helper: a neutral wavenumber above two on every large log-annulus

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

Step of B0034 (`paper/main.tex`, lines 1009–1014; blueprint units B0032, B0033):
"A compactly supported approximation ... retains its negative `𝓗₂` form. It follows
that `α_{max,N} > 2` for every sufficiently large `N`." Here the largest neutral
wavenumber is produced directly as a Dirichlet eigenvalue of `-∂² - W` on `[-N, N]`:
`neutralReal α (-N) N = 0` with `α > 2` (`exists_neutral_gt_two`).

Proof (shooting). The compact trial `f` of B0033 (`exists_compact_negative_trial`,
support in `(-R, R)`) has a negative `𝓗_{α₁}` form for some `α₁ > 2`. By the
ground-state identity (`groundState_form_nonneg`) the neutral solution at any such
`α₁` vanishes inside `(-R, R)`. At `α = 3 > √8 ≥ √W` it has no zero in `(a, b]`
(integration by parts). Let `α_*` be the largest `α ∈ [α₁, 3]` for which the neutral
solution is `≤ 0` somewhere in `[a + δ, b]` (compactness, joint continuity). Then the
solution at `α_*` is `≥ 0` on `(a, b]` with a zero; an interior zero would be a double
zero, so the zero is at `b`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh UnforcedLeray.Rayleigh.Evans UnforcedLeray.Sturm
open UnforcedLeray.GaussianPotential NonUniqueEuler.LinODE

/-- Joint continuity of the neutral normalized pair in the wavenumber and the radius. -/
theorem continuous_neutralPair_joint (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => neutralNormalizedPair p.1 a p.2) := by
  have hV : ContinuousOn (Function.uncurry (fun (t γ : ℝ) => neutralPotential γ t))
      (univ ×ˢ univ) := by
    apply Continuous.continuousOn
    have h1 : Continuous (fun q : ℝ × ℝ => ((q.2 : ℂ)) ^ 2) := by fun_prop
    have h2 : Continuous (fun q : ℝ × ℝ => ((Wlog q.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_Wlog.comp continuous_fst)
    exact h1.sub h2
  have h := continuousOn_sol hV a (y₀ := fun _ : ℝ => ((0 : ℂ), (1 : ℂ))) continuousOn_const
  rw [univ_prod_univ] at h
  have hc := continuousOn_univ.mp h
  exact hc.comp continuous_swap

theorem continuous_neutralReal_joint (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => neutralReal p.1 a p.2) :=
  Complex.continuous_re.comp (continuous_fst.comp (continuous_neutralPair_joint a))

theorem continuous_neutralRealDeriv_joint (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => neutralRealDeriv p.1 a p.2) :=
  Complex.continuous_re.comp (continuous_snd.comp (continuous_neutralPair_joint a))

theorem neutralReal_smooth (α a : ℝ) : ContDiff ℝ ∞ (neutralReal α a) :=
  Complex.reCLM.contDiff.comp (neutralNormalizedF_smooth α a)

theorem deriv_neutralReal (α a : ℝ) : deriv (neutralReal α a) = neutralRealDeriv α a :=
  funext fun t => (hasDerivAt_neutralReal α a t).deriv

/-- A neutral normalized solution with a negative form on a compact trial vanishes
inside the trial's support. -/
theorem exists_zero_of_negative_form {α a : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f)
    (hint : Integrable (fun t => deriv f t ^ 2 + (α ^ 2 - Wlog t) * f t ^ 2))
    (hneg : (∫ t, deriv f t ^ 2 + (α ^ 2 - Wlog t) * f t ^ 2) < 0) :
    ∃ τ ∈ tsupport f, neutralReal α a τ = 0 := by
  by_contra hno
  push Not at hno
  have hnn := UnforcedLeray.Sturm.groundState_form_nonneg (h := neutralReal α a)
    (V := fun t => α ^ 2 - Wlog t) (neutralReal_smooth α a) hf hfc hno
    (fun t _ => by
      rw [deriv_neutralReal]
      exact (hasDerivAt_neutralRealDeriv α a t).deriv) hint
  linarith

/-- For `α ≥ 3` the neutral normalized solution has no zero in `(a, b]`. -/
theorem neutralReal_ne_zero_of_three_le {α a ζ : ℝ} (hα : 3 ≤ α) (haζ : a < ζ)
    (hpos : ∃ t ∈ Ioo a ζ, neutralRealDeriv α a t ≠ 0) : neutralReal α a ζ ≠ 0 := by
  intro hz
  have hd : ∀ t, HasDerivAt (fun s => neutralReal α a s * neutralRealDeriv α a s)
      (neutralRealDeriv α a t ^ 2 + (α ^ 2 - Wlog t) * neutralReal α a t ^ 2) t := fun t => by
    have h := (hasDerivAt_neutralReal α a t).mul (hasDerivAt_neutralRealDeriv α a t)
    refine h.congr_deriv ?_
    ring
  have hc1 : Continuous (fun t => neutralRealDeriv α a t ^ 2) :=
    (continuous_neutralRealDeriv α a).pow 2
  have hcont : Continuous (fun t =>
      neutralRealDeriv α a t ^ 2 + (α ^ 2 - Wlog t) * neutralReal α a t ^ 2) :=
    hc1.add ((continuous_const.sub continuous_Wlog).mul ((continuous_neutralReal α a).pow 2))
  have hibp := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hcont.intervalIntegrable a ζ)
  have hga : neutralReal α a a = 0 := neutralReal_initial α a
  rw [hz, hga, zero_mul, zero_mul, sub_zero] at hibp
  have hle : (∫ t in a..ζ, neutralRealDeriv α a t ^ 2) ≤
      ∫ t in a..ζ, neutralRealDeriv α a t ^ 2 + (α ^ 2 - Wlog t) * neutralReal α a t ^ 2 := by
    apply intervalIntegral.integral_mono_on haζ.le (hc1.intervalIntegrable a ζ)
      (hcont.intervalIntegrable a ζ)
    intro t _
    have hW := Wlog_le_eight t
    have : 0 ≤ (α ^ 2 - Wlog t) * neutralReal α a t ^ 2 :=
      mul_nonneg (by nlinarith) (sq_nonneg _)
    linarith
  have hnn : 0 ≤ ∫ t in a..ζ, neutralRealDeriv α a t ^ 2 :=
    intervalIntegral.integral_nonneg haζ.le (fun t _ => sq_nonneg _)
  have h0 : (∫ t in a..ζ, neutralRealDeriv α a t ^ 2) = 0 := by linarith
  obtain ⟨t, ht, hne⟩ := hpos
  exact hne (eq_zero_of_integral_sq_eq_zero (continuous_neutralRealDeriv α a).continuousOn
    h0 t ht)

theorem integrable_trial_form {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (α : ℝ) : Integrable (fun t => deriv f t ^ 2 + (α ^ 2 - Wlog t) * f t ^ 2) := by
  have hcd : Continuous (deriv f) := hf.continuous_deriv le_rfl
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hcd.pow 2).add ((continuous_const.sub continuous_Wlog).mul (hf.continuous.pow 2))
  · apply HasCompactSupport.intro hfc (fun t ht => ?_)
    have h1 : f t = 0 := image_eq_zero_of_notMem_tsupport ht
    have h2 : deriv f t = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => ht (tsupport_deriv_subset h))
    simp [h1, h2]

/-- B0033 in the form used here: some `α₁ > 2` has a negative form on a compact trial
supported in `(-R, R)`. -/
theorem exists_trial_alpha :
    ∃ R : ℝ, 0 < R ∧ ∃ f : ℝ → ℝ, ContDiff ℝ 1 f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo (-R) R ∧ ∃ α₁ : ℝ, 2 < α₁ ∧ α₁ < 3 ∧
        (∫ t, deriv f t ^ 2 + (α₁ ^ 2 - Wlog t) * f t ^ 2) < 0 := by
  obtain ⟨R, hR, f, hf, hfc, hfs, -, -, hQ⟩ :=
    UnforcedLeray.GaussianCompactTrial.exists_compact_negative_trial
  refine ⟨R, hR, f, hf, hfc, hfs, ?_⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = ∫ t, UnforcedLeray.GaussianCompactTrial.quadraticIntegrand f t :=
    ⟨_, rfl⟩
  rw [← hQdef] at hQ
  obtain ⟨m, hm⟩ : ∃ m, m = ∫ t, f t ^ 2 := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; exact integral_nonneg (fun t => sq_nonneg _)
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min 1 (-Q / (2 * (m + 1))) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact lt_min one_pos (div_pos (by linarith) (by linarith))
  have hη1 : η ≤ 1 := by rw [hη]; exact min_le_left _ _
  have hη2 : η ≤ -Q / (2 * (m + 1)) := by rw [hη]; exact min_le_right _ _
  refine ⟨Real.sqrt (4 + η), ?_, ?_, ?_⟩
  · rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  · rw [show (3 : ℝ) = Real.sqrt 9 by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  · have hsq : Real.sqrt (4 + η) ^ 2 = 4 + η := Real.sq_sqrt (by linarith)
    have hint4 := integrable_trial_form hf hfc 2
    have hf2 : Integrable (fun t => f t ^ 2) := by
      apply Continuous.integrable_of_hasCompactSupport (hf.continuous.pow 2)
      apply HasCompactSupport.intro hfc (fun t ht => ?_)
      simp [image_eq_zero_of_notMem_tsupport ht]
    have heq : (fun t => deriv f t ^ 2 + (Real.sqrt (4 + η) ^ 2 - Wlog t) * f t ^ 2) =
        fun t => (deriv f t ^ 2 + ((2 : ℝ) ^ 2 - Wlog t) * f t ^ 2) + η * f t ^ 2 := by
      funext t
      rw [hsq]
      ring
    have hQ' : (∫ t, deriv f t ^ 2 + ((2 : ℝ) ^ 2 - Wlog t) * f t ^ 2) = Q := by
      rw [hQdef]
      congr 1
      funext t
      simp only [UnforcedLeray.GaussianCompactTrial.quadraticIntegrand]
      norm_num
    rw [heq, integral_add hint4 (hf2.const_mul η), integral_const_mul, hQ', ← hm]
    have hηm : η * m ≤ -Q / (2 * (m + 1)) * m := mul_le_mul_of_nonneg_right hη2 hm0
    have hfrac : -Q / (2 * (m + 1)) * m ≤ -Q / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith

/-- B0034, neutral step: on every log-annulus `[-N, N]` with `N` beyond the support of
the compact trial, there is a neutral wavenumber `α > 2`. -/
theorem exists_neutral_gt_two :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ N : ℝ, R₀ < N → ∃ α : ℝ, 2 < α ∧ neutralReal α (-N) N = 0 := by
  obtain ⟨R, hR, f, hf, hfc, hfs, α₁, hα₁, hα₁3, hneg⟩ := exists_trial_alpha
  refine ⟨R, hR, fun N hN => ?_⟩
  set a : ℝ := -N with ha
  set b : ℝ := N with hb
  have hab : a < b := by linarith
  set Kγ : Set ℝ := Icc α₁ 3 with hKγ
  -- uniform positivity of the slope near `a`
  have htube : ∀ᶠ t in 𝓝 a, ∀ γ ∈ Kγ, 0 < neutralRealDeriv γ a t := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro γ _
    have hc : ContinuousAt (fun z : ℝ × ℝ => neutralRealDeriv z.2 a z.1) (a, γ) :=
      ((continuous_neutralRealDeriv_joint a).comp continuous_swap).continuousAt
    have h1 : neutralRealDeriv γ a a = 1 := neutralRealDeriv_initial γ a
    exact hc.eventually (lt_mem_nhds (by simp))
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.eventually_nhds_iff.mp htube
  set δ : ℝ := min (δ₀ / 2) ((N - R) / 2) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδR : a + δ < -R := by
    have := min_le_right (δ₀ / 2) ((N - R) / 2)
    linarith
  have hderivpos : ∀ γ ∈ Kγ, ∀ t ∈ Icc a (a + δ), 0 < neutralRealDeriv γ a t := by
    intro γ hγ t ht
    apply hδ₀' _ γ hγ
    rw [Real.dist_eq, abs_lt]
    have := min_le_left (δ₀ / 2) ((N - R) / 2)
    constructor <;> linarith [ht.1, ht.2]
  have hnearpos : ∀ γ ∈ Kγ, ∀ t ∈ Ioc a (a + δ), 0 < neutralReal γ a t := by
    intro γ hγ t ht
    have hmono : StrictMonoOn (neutralReal γ a) (Icc a (a + δ)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_neutralReal γ a).continuousOn
      intro x hx
      rw [interior_Icc] at hx
      rw [deriv_neutralReal]
      exact hderivpos γ hγ x (Ioo_subset_Icc_self hx)
    have := hmono (left_mem_Icc.mpr (by linarith : a ≤ a + δ)) ⟨ht.1.le, ht.2⟩ ht.1
    simpa using this
  -- the compact set of wavenumbers with a nonpositive value on `[a + δ, b]`
  set Kt : Set ℝ := Icc (a + δ) b with hKt
  set T : Set (ℝ × ℝ) := (Kγ ×ˢ Kt) ∩ {p | neutralReal p.1 a p.2 ≤ 0} with hT
  have hTc : IsCompact T :=
    (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le (continuous_neutralReal_joint a) continuous_const)
  set S : Set ℝ := Prod.fst '' T with hS
  have hSc : IsCompact S := hTc.image continuous_fst
  -- `α₁ ∈ S`
  obtain ⟨τ₁, hτ₁, hτ₁z⟩ := exists_zero_of_negative_form (a := a) hf hfc
    (integrable_trial_form hf hfc α₁) hneg
  have hτ₁' := hfs hτ₁
  have hα₁S : α₁ ∈ S := by
    refine ⟨(α₁, τ₁), ⟨⟨⟨le_rfl, by linarith⟩, ?_, ?_⟩, ?_⟩, rfl⟩
    · linarith [hτ₁'.1]
    · linarith [hτ₁'.2]
    · simp [hτ₁z]
  have hSne : S.Nonempty := ⟨α₁, hα₁S⟩
  set γs := sSup S with hγs
  have hγsS : γs ∈ S := hSc.sSup_mem hSne
  obtain ⟨⟨γ', τ₀⟩, ⟨⟨hγ'K, hτ₀K⟩, hτ₀le⟩, hγ'eq⟩ := hγsS
  simp only at hγ'eq hτ₀le
  subst hγ'eq
  have hbdd : BddAbove S := hSc.bddAbove
  -- `3 ∉ S`
  have h3K : (3 : ℝ) ∈ Kγ := ⟨by linarith, le_rfl⟩
  have h3S : (3 : ℝ) ∉ S := by
    rintro ⟨⟨γ3, τ⟩, ⟨⟨hγ3K, hτK⟩, hτle⟩, hγ3eq⟩
    simp only at hγ3eq hτle
    subst hγ3eq
    have hpos1 : 0 < neutralReal 3 a (a + δ) :=
      hnearpos 3 h3K (a + δ) ⟨by linarith, le_rfl⟩
    have hsub : Icc (a + δ) τ ⊆ Icc a b := Icc_subset_Icc (by linarith) hτK.2
    obtain ⟨ζ, hζ, hζz⟩ : ∃ ζ ∈ Icc (a + δ) τ, neutralReal 3 a ζ = 0 := by
      have hivt := intermediate_value_Icc' hτK.1 (continuous_neutralReal 3 a).continuousOn
      exact hivt ⟨hτle, hpos1.le⟩
    apply neutralReal_ne_zero_of_three_le le_rfl (by linarith [hζ.1] : a < ζ) _ hζz
    refine ⟨a + δ / 2, ⟨by linarith, by linarith [hζ.1]⟩, ?_⟩
    exact (hderivpos 3 h3K (a + δ / 2) ⟨by linarith, by linarith⟩).ne'
  have hγslt : γs < 3 := by
    rcases hγ'K.2.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ ⟨(γs, τ₀), ⟨⟨hγ'K, hτ₀K⟩, hτ₀le⟩, rfl⟩ : (3 : ℝ) ∈ S) h3S
  -- above `γs` the solution is positive on `[a + δ, b]`
  have habove : ∀ γ, γs < γ → γ ≤ 3 → ∀ t ∈ Kt, 0 < neutralReal γ a t := by
    intro γ hγ hγ3 t ht
    by_contra hle
    push Not at hle
    have hmem : γ ∈ S := ⟨(γ, t), ⟨⟨⟨by linarith [hγ'K.1], hγ3⟩, ht⟩, hle⟩, rfl⟩
    exact absurd (le_csSup hbdd hmem) (not_le.mpr hγ)
  have hnonneg : ∀ t ∈ Kt, 0 ≤ neutralReal γs a t := by
    intro t ht
    have hc : ContinuousAt (fun γ => neutralReal γ a t) γs :=
      ((continuous_neutralReal_joint a).comp (continuous_id.prodMk continuous_const)).continuousAt
    have hlim := hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] γs ≤ 𝓝 γs)
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT hγslt] with γ hγ
    exact (habove γ hγ.1 hγ.2.le t ht).le
  have hτ₀z : neutralReal γs a τ₀ = 0 := le_antisymm hτ₀le (hnonneg τ₀ hτ₀K)
  -- the zero is at `b`
  have hτ₀b : τ₀ = b := by
    by_contra hne
    have hτ₀lt : τ₀ < b := lt_of_le_of_ne hτ₀K.2 hne
    have hτ₀a : a < τ₀ := by linarith [hτ₀K.1]
    have hmin : IsLocalMin (neutralReal γs a) τ₀ := by
      filter_upwards [Ioo_mem_nhds hτ₀a hτ₀lt] with t ht
      rw [hτ₀z]
      by_cases htd : t ≤ a + δ
      · exact (hnearpos γs hγ'K t ⟨ht.1, htd⟩).le
      · exact hnonneg t ⟨(not_le.mp htd).le, ht.2.le⟩
    have hd0 : neutralRealDeriv γs a τ₀ = 0 := hmin.hasDerivAt_eq_zero (hasDerivAt_neutralReal γs a τ₀)
    have hreal := neutralNormalizedF_eq_ofReal γs a τ₀
    apply neutralNormalizedDerivative_ne_zero_of_value_zero γs a τ₀
    · rw [hreal.1, hτ₀z, Complex.ofReal_zero]
    · rw [hreal.2, hd0, Complex.ofReal_zero]
  refine ⟨γs, lt_of_lt_of_le hα₁ hγ'K.1, ?_⟩
  rw [← hτ₀b]
  exact hτ₀z

end UnforcedLeray.ComplexODEB
