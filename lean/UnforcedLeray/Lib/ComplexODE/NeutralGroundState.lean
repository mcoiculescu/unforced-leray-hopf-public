import UnforcedLeray.Lib.ComplexODE.NeutralReal
import UnforcedLeray.GaussianCompactTrial
import UnforcedLeray.Analysis.Sturm.NeutralFactorizationBasic

/-!
# The annular neutral ground state (INF18 target O1)

Wave 1 block 1H part 3, scoping note

bypass B8 (i). Blueprint unit B0034 (`paper/main.tex` lines 1001--1021): on the log-annulus
`(-N, N)` the threshold `α_{max,N}` of eq. st18-t00032 satisfies `α_{max,N} > 2` for all large
`N`; it is attained by a Dirichlet solution of `F'' = (α² - W) F`.

Instead of the min--max principle (`paper/main.tex` lines 1001--1011, Teschl Thm 4.10) and
the counting of eq. st18-t00030 (lines 941--948, B0028--B0029), the proof is by ODE:

* **No interior zero above 1** (`neutralU_pos_of_dirichlet`). If `β² > 1` and the normalized
  neutral solution vanishes at both ends of `[a, b] ∋ t_*`, it is positive inside. Two zeros
  on one side of `t_*` contradict Sturm comparison with the explicit profile
  `h_* = e^t (Ω - a_*)` (eq. st18-t00028), which solves `h'' = (1 - W) h` and vanishes only at
  `t_*`. This is the ODE form of eq. st18-t00029--t00030.
* **Uniqueness above 1** (`neutral_dirichlet_unique`): two positive Dirichlet solutions with
  `β₁ < β₂` contradict Sturm comparison.
* **Existence above 2** (`exists_neutral_dirichlet_above`). The compiled compact trial
  `GaussianCompactTrial.exists_compact_negative_trial` (the manuscript's compactly supported
  approximation, line 1009) has negative form at some `β₀ > 2`. A solution positive on the
  trial's support would make that form nonnegative (compiled ground-state factorization
  `groundState_form_nonneg`, the identity eq. st18-t00029). Positivity on `(-N, N]` holds at
  `β = 3` (Sturm comparison with `t + N`), and the set of such `β ∈ [β₀, 3]` is closed and
  relatively open as long as no Dirichlet zero occurs; so a Dirichlet zero lies in `[β₀, 3]`.

Main result: `exists_dirichlet_neutral`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.ComplexODE

/-- **Sturm comparison, second zero.** If `u'' = q_u u` has a simple zero at `p` and a zero at
`q > p`, and a solution `h` of `h'' = q_h h` with `q_h < q_u` is positive on `(p, q)`, this is
contradictory. -/
theorem sturm_no_second_zero {u u' h h' qu qh : ℝ → ℝ} {p q : ℝ} (hpq : p < q)
    (hu : ∀ t, HasDerivAt u (u' t) t) (hu' : ∀ t, HasDerivAt u' (qu t * u t) t)
    (hh : ∀ t, HasDerivAt h (h' t) t) (hh' : ∀ t, HasDerivAt h' (qh t * h t) t)
    (hqu : Continuous qu) (hqh : Continuous qh)
    (hlt : ∀ t ∈ Ioo p q, qh t < qu t)
    (hup : u p = 0) (hu'p : u' p ≠ 0) (huq : u q = 0)
    (hhpos : ∀ t ∈ Ioo p q, 0 < h t) : False := by
  have huc : Continuous u := continuous_iff_continuousAt.2 fun t => (hu t).continuousAt
  have key : ∀ {v v' : ℝ → ℝ}, (∀ t, HasDerivAt v (v' t) t) →
      (∀ t, HasDerivAt v' (qu t * v t) t) → Continuous v → v p = 0 → 0 < v' p → v q = 0 →
      False := by
    intro v v' hv hv' hvc hvp hv'p hvq
    obtain ⟨r, hr, hr0, hrpos⟩ := exists_first_zero hvc hpq
      (exists_pos_Ioo_of_hasDerivAt_pos (hv p) hvp hv'p) hvq.le
    exact sturm_comparison_false hr.1 hv hv' hh hh' hqu hqh
      (fun t ht => hlt t ⟨ht.1, ht.2.trans_le hr.2⟩) hvp hr0 hrpos
      (fun t ht => hhpos t ⟨ht.1, ht.2.trans_le hr.2⟩)
  rcases lt_or_gt_of_ne hu'p with hneg | hpos
  · exact key (v := fun t => -u t) (v' := fun t => -u' t)
      (fun t => (hu t).neg) (fun t => by
        have h1 := (hu' t).neg
        rw [← mul_neg] at h1
        exact h1) huc.neg
      (by simp [hup]) (neg_pos.mpr hneg) (by simp [huq])
  · exact key hu hu' huc hup hpos huq

end UnforcedLeray.ComplexODE

namespace UnforcedLeray.Rayleigh.Evans

open UnforcedLeray.ComplexODE Sturm GaussianPotential

theorem neutralU_pos_start (β a : ℝ) : ∃ δ > 0, ∀ t ∈ Ioo a (a + δ), 0 < neutralU β a t :=
  exists_pos_Ioo_of_hasDerivAt_pos (hasDerivAt_neutralU β a a) (neutralU_initial β a)
    (by rw [neutralU'_initial]; exact one_pos)

theorem continuous_neutralCoefficient (β : ℝ) : Continuous (fun t => β ^ 2 - Wlog t) :=
  continuous_const.sub continuous_Wlog

theorem hasDerivAt_neutralProfile_deriv (t : ℝ) :
    HasDerivAt neutralProfile (deriv neutralProfile t) t :=
  (neutralProfile_smooth.differentiable (by simp) t).hasDerivAt

/-- **No interior zero above 1.** If `β² > 1` and the normalized neutral solution started at
`a` vanishes at `b`, then it is positive on `(a, b)`. When `a < t_* < b` it therefore does not
vanish at the critical log-radius `t_*` (the conclusion of eq. st18-t00030 used in
bypass B8 (i)). The position of `t_*` is not needed for positivity: a zero `t₁ ≤ t_*` is
compared with `h_* > 0` on `(a, t₁)`, a zero `t₁ > t_*` with `-h_* > 0` on `(t₁, b)`. -/
theorem neutralU_pos_of_dirichlet {β a b : ℝ} (hβ : 1 < β ^ 2) (hD : neutralU β a b = 0) :
    ∀ t ∈ Ioo a b, 0 < neutralU β a t := by
  have hne : ∀ t ∈ Ioo a b, neutralU β a t ≠ 0 := by
    intro t₁ ht₁ h0
    rcases le_or_gt t₁ neutralCriticalTime with hle | hgt
    · exact sturm_no_second_zero ht₁.1 (hasDerivAt_neutralU β a) (hasDerivAt_neutralU' β a)
        hasDerivAt_neutralProfile_deriv hasDerivAt_neutralProfile'
        (continuous_neutralCoefficient β) (continuous_const.sub continuous_Wlog)
        (fun t _ => by linarith) (neutralU_initial β a)
        (by rw [neutralU'_initial]; exact one_ne_zero) h0
        (fun t ht => neutralProfile_pos_of_lt (ht.2.trans_le hle))
    · exact sturm_no_second_zero ht₁.2 (hasDerivAt_neutralU β a) (hasDerivAt_neutralU' β a)
        (h := fun t => -neutralProfile t) (h' := fun t => -deriv neutralProfile t)
        (qh := fun t => 1 - Wlog t)
        (fun t => (hasDerivAt_neutralProfile_deriv t).neg)
        (fun t => by
          have h1 := (hasDerivAt_neutralProfile' t).neg
          rw [← mul_neg] at h1
          exact h1)
        (continuous_neutralCoefficient β) (continuous_const.sub continuous_Wlog)
        (fun t _ => by show 1 - Wlog t < β ^ 2 - Wlog t; linarith) h0
        (neutralU'_ne_zero_of_eq_zero h0) hD
        (fun t ht => neg_pos.mpr (neutralProfile_neg_of_gt (hgt.trans ht.1)))
  intro t ht
  by_contra hle
  obtain ⟨r, hr, hr0, -⟩ := exists_first_zero (continuous_neutralU β a) ht.1
    (neutralU_pos_start β a) (not_lt.mp hle)
  exact hne r ⟨hr.1, hr.2.trans_lt ht.2⟩ hr0

/-- **Uniqueness above 1.** Two neutral Dirichlet wavenumbers above `1` on `[a, b]`
coincide. -/
theorem neutral_dirichlet_unique {β₁ β₂ a b : ℝ} (h₁ : 1 < β₁) (h₂ : 1 < β₂) (hab : a < b)
    (hD₁ : neutralU β₁ a b = 0) (hD₂ : neutralU β₂ a b = 0) : β₁ = β₂ := by
  have key : ∀ {x y : ℝ}, 1 < x → 1 < y → x < y → neutralU x a b = 0 →
      neutralU y a b = 0 → False := by
    intro x y hx hy hxy hDx hDy
    have hx2 : 1 < x ^ 2 := by nlinarith
    have hy2 : 1 < y ^ 2 := by nlinarith
    exact sturm_comparison_false hab (hasDerivAt_neutralU y a) (hasDerivAt_neutralU' y a)
      (hasDerivAt_neutralU x a) (hasDerivAt_neutralU' x a)
      (continuous_neutralCoefficient y) (continuous_neutralCoefficient x)
      (fun t _ => by nlinarith) (neutralU_initial y a) hDy
      (neutralU_pos_of_dirichlet hy2 hDy) (neutralU_pos_of_dirichlet hx2 hDx)
  rcases lt_trichotomy β₁ β₂ with h | h | h
  · exact (key h₁ h₂ h hD₁ hD₂).elim
  · exact h
  · exact (key h₂ h₁ h hD₂ hD₁).elim

/-- At `β = 3` (`β² > 8 ≥ W`) the normalized neutral solution is positive after `a`
(Sturm comparison with `t - a`). -/
theorem neutralU_three_pos (a : ℝ) : ∀ t ∈ Ioi a, 0 < neutralU 3 a t := by
  intro t₁ ht₁
  by_contra hle
  obtain ⟨r, hr, hr0, hrpos⟩ := exists_first_zero (continuous_neutralU 3 a) ht₁
    (neutralU_pos_start 3 a) (not_lt.mp hle)
  exact sturm_comparison_false hr.1 (hasDerivAt_neutralU 3 a) (hasDerivAt_neutralU' 3 a)
    (h := fun t => t - a) (h' := fun _ => 1) (qh := fun _ => 0)
    (fun t => (hasDerivAt_id' t).sub_const a)
    (fun t => by simpa using hasDerivAt_const t (1 : ℝ))
    (continuous_neutralCoefficient 3) continuous_const
    (fun t _ => by
      have h8 := Wlog_le_eight t
      have h9 : (3 : ℝ) ^ 2 = 9 := by norm_num
      show (0 : ℝ) < 3 ^ 2 - Wlog t
      linarith)
    (neutralU_initial 3 a) hr0 hrpos (fun t ht => sub_pos.mpr ht.1)

/-- Positivity on `(a, b]` is an open condition on `β`. -/
theorem eventually_neutralU_pos {x a b : ℝ}
    (hx : ∀ t ∈ Ioc a b, 0 < neutralU x a t) :
    ∀ᶠ β in 𝓝 x, ∀ t ∈ Ioc a b, 0 < neutralU β a t := by
  have hU' : Continuous (fun z : ℝ × ℝ => neutralU' z.1 a z.2) := by
    have h := (continuous_neutralU'_joint a).comp (continuous_snd.prodMk continuous_fst)
    exact h
  have hU : Continuous (fun z : ℝ × ℝ => neutralU z.1 a z.2) := by
    have h := (continuous_neutralU_joint a).comp (continuous_snd.prodMk continuous_fst)
    exact h
  obtain ⟨δ, hδ, hδU'⟩ : ∃ δ > 0, ∀ t ∈ Icc a (a + δ), 0 < neutralU' x a t := by
    have hev : ∀ᶠ t in 𝓝 a, 0 < neutralU' x a t :=
      ((continuous_neutralU' x a).continuousAt.tendsto).eventually
        (lt_mem_nhds (by rw [neutralU'_initial]; exact one_pos))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨ε / 2, by positivity, fun t ht => hball ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have h1 : ∀ᶠ β in 𝓝 x, ∀ t ∈ Icc a (a + δ), 0 < neutralU' β a t :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun t ht =>
      (hU'.continuousAt (x := (x, t)).tendsto).eventually (lt_mem_nhds (hδU' t ht))
  have h2 : ∀ᶠ β in 𝓝 x, ∀ t ∈ Icc (a + δ) b, 0 < neutralU β a t :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun t ht =>
      (hU.continuousAt (x := (x, t)).tendsto).eventually
        (lt_mem_nhds (hx t ⟨by linarith [ht.1], ht.2⟩))
  filter_upwards [h1, h2] with β hβ1 hβ2
  intro t ht
  rcases le_or_gt t (a + δ) with hle | hlt
  · have hmono : StrictMonoOn (neutralU β a) (Icc a (a + δ)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_neutralU β a).continuousOn
      intro s hs
      rw [interior_Icc] at hs
      rw [deriv_neutralU]
      exact hβ1 s (Ioo_subset_Icc_self hs)
    have h := hmono ⟨le_rfl, by linarith⟩ ⟨ht.1.le, hle⟩ ht.1
    rwa [neutralU_initial] at h
  · exact hβ2 t ⟨hlt.le, ht.2⟩

/-- Away from Dirichlet zeros, positivity on `(a, b]` is a closed condition on `[β₀, β₁]`. -/
theorem isClosed_neutralPos_inter {a b β₀ β₁ : ℝ} (hab : a < b)
    (hH : ∀ β ∈ Icc β₀ β₁, neutralU β a b ≠ 0) :
    IsClosed ({β | ∀ t ∈ Ioc a b, 0 < neutralU β a t} ∩ Icc β₀ β₁) := by
  have hT : IsClosed ({β | ∀ t ∈ Ioc a b, 0 ≤ neutralU β a t} ∩ Icc β₀ β₁) := by
    apply IsClosed.inter _ isClosed_Icc
    have hset : {β | ∀ t ∈ Ioc a b, 0 ≤ neutralU β a t} =
        ⋂ t ∈ Ioc a b, {β | 0 ≤ neutralU β a t} := by
      ext β
      simp
    rw [hset]
    refine isClosed_biInter fun t _ => isClosed_le continuous_const ?_
    have h := (continuous_neutralU_joint a).comp
      ((continuous_const : Continuous fun _ : ℝ => t).prodMk continuous_id)
    exact h
  convert hT using 1
  ext β
  constructor
  · rintro ⟨hpos, hI⟩
    exact ⟨fun t ht => (hpos t ht).le, hI⟩
  · rintro ⟨hnn, hI⟩
    refine ⟨fun t ht => ?_, hI⟩
    rcases eq_or_lt_of_le ht.2 with heq | hlt
    · rw [heq]
      exact lt_of_le_of_ne (hnn b ⟨hab, le_rfl⟩) (Ne.symm (hH β hI))
    · rcases eq_or_lt_of_le (hnn t ht) with h0 | hp
      · exfalso
        have hmin : IsLocalMin (neutralU β a) t :=
          Filter.eventually_of_mem (Ioo_mem_nhds ht.1 hlt) fun s hs => by
            rw [← h0]
            exact hnn s ⟨hs.1, hs.2.le⟩
        exact neutralU'_ne_zero_of_eq_zero h0.symm
          (hmin.hasDerivAt_eq_zero (hasDerivAt_neutralU β a t))
      · exact hp

/-- **Shooting.** If the normalized neutral solution at `β₀ ≤ 3` is not positive on `(a, b]`,
there is a Dirichlet wavenumber in `[β₀, 3]`. -/
theorem exists_neutral_dirichlet_of_not_pos {a b β₀ : ℝ} (hab : a < b) (hβ₀ : β₀ ≤ 3)
    (hnot : ¬ ∀ t ∈ Ioc a b, 0 < neutralU β₀ a t) :
    ∃ β ∈ Icc β₀ 3, neutralU β a b = 0 := by
  by_contra hH
  have hH' : ∀ β ∈ Icc β₀ 3, neutralU β a b ≠ 0 := fun β hβ h0 => hH ⟨β, hβ, h0⟩
  apply hnot
  refine IsClosed.mem_of_ge_of_forall_exists_lt (s := {β | ∀ t ∈ Ioc a b, 0 < neutralU β a t})
    (isClosed_neutralPos_inter hab hH') (fun t ht => neutralU_three_pos a t ht.1) hβ₀ ?_
  rintro x ⟨hxS, hxI⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_neutralU_pos hxS)
  refine ⟨max β₀ (x - ε / 2), hball ?_, le_max_left _ _, max_lt hxI.1 (by linarith)⟩
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor
  · have := max_le hxI.1.le (by linarith : x - ε / 2 ≤ x)
    linarith
  · linarith [le_max_right β₀ (x - ε / 2)]

/-- The compiled negative trial gives `β₀ ∈ (2, 3]` and `R > 0` such that, on every
log-annulus `(-N, N)` with `N ≥ R`, the normalized neutral solution at `β₀` is not positive on
`(-N, N]` (`paper/main.tex` lines 1008--1011). -/
theorem exists_trial_wavenumber : ∃ R > 0, ∃ β₀ : ℝ, 2 < β₀ ∧ β₀ ≤ 3 ∧
    ∀ N : ℝ, R ≤ N → ¬ ∀ t ∈ Ioc (-N) N, 0 < neutralU β₀ (-N) t := by
  obtain ⟨R, hR, f, hf, hfc, hsupp, hf2, hdf2, hQ⟩ :=
    GaussianCompactTrial.exists_compact_negative_trial
  set Q := ∫ t : ℝ, GaussianCompactTrial.quadraticIntegrand f t with hQdef
  set M := ∫ t : ℝ, f t ^ 2 with hMdef
  have hM : 0 ≤ M := integral_nonneg fun t => sq_nonneg _
  set ε := min 1 (-Q / (2 * (M + 1))) with hεdef
  have hε : 0 < ε := lt_min one_pos (div_pos (by linarith) (by positivity))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεQ : ε * (M + 1) ≤ -Q / 2 := by
    have h := min_le_right 1 (-Q / (2 * (M + 1)))
    rw [← hεdef] at h
    have hM1 : 0 < M + 1 := by linarith
    calc ε * (M + 1) ≤ -Q / (2 * (M + 1)) * (M + 1) := mul_le_mul_of_nonneg_right h hM1.le
      _ = -Q / 2 := by field_simp
  set β₀ := Real.sqrt (4 + ε) with hβ₀def
  have hβ₀sq : β₀ ^ 2 = 4 + ε := Real.sq_sqrt (by linarith)
  have hβ₀2 : 2 < β₀ := by
    rw [hβ₀def, show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hβ₀3 : β₀ ≤ 3 := by
    rw [hβ₀def, show (3 : ℝ) = Real.sqrt (3 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  refine ⟨R, hR, β₀, hβ₀2, hβ₀3, fun N hN hpos => ?_⟩
  have hbound : ∀ t, ‖β₀ ^ 2 - Wlog t‖ ≤ β₀ ^ 2 + 8 := by
    intro t
    rw [Real.norm_eq_abs, abs_le]
    have h0 := Wlog_pos t
    have h8 := Wlog_le_eight t
    constructor <;> nlinarith
  have hbound4 : ∀ t, ‖4 - Wlog t‖ ≤ 12 := by
    intro t
    rw [Real.norm_eq_abs, abs_le]
    have h0 := Wlog_pos t
    have h8 := Wlog_le_eight t
    constructor <;> linarith
  have hint1 : Integrable (fun t => (β₀ ^ 2 - Wlog t) * f t ^ 2) :=
    hf2.integrable_sq.bdd_mul (continuous_neutralCoefficient β₀).aestronglyMeasurable
      (Eventually.of_forall hbound)
  have hint4 : Integrable (fun t => (4 - Wlog t) * f t ^ 2) :=
    hf2.integrable_sq.bdd_mul (continuous_const.sub continuous_Wlog).aestronglyMeasurable
      (Eventually.of_forall hbound4)
  have hform : Integrable (fun t => deriv f t ^ 2 + (β₀ ^ 2 - Wlog t) * f t ^ 2) :=
    hdf2.integrable_sq.add hint1
  have hnonneg : 0 ≤ ∫ t, deriv f t ^ 2 + (β₀ ^ 2 - Wlog t) * f t ^ 2 := by
    apply groundState_form_nonneg (h := neutralU β₀ (-N)) (neutralU_contDiff β₀ (-N)) hf hfc
    · intro t ht
      have ht' := hsupp ht
      exact (hpos t ⟨by linarith [ht'.1], by linarith [ht'.2]⟩).ne'
    · intro t _
      exact deriv_deriv_neutralU β₀ (-N) t
    · exact hform
  have hsplit : (∫ t, deriv f t ^ 2 + (β₀ ^ 2 - Wlog t) * f t ^ 2) = Q + ε * M := by
    have hpt : (fun t => deriv f t ^ 2 + (β₀ ^ 2 - Wlog t) * f t ^ 2) =
        fun t => GaussianCompactTrial.quadraticIntegrand f t + ε * f t ^ 2 := by
      funext t
      unfold GaussianCompactTrial.quadraticIntegrand
      rw [hβ₀sq]
      ring
    have hq : Integrable (fun t => GaussianCompactTrial.quadraticIntegrand f t) :=
      hdf2.integrable_sq.add hint4
    rw [hpt, integral_add hq (hf2.integrable_sq.const_mul ε), integral_const_mul]
  have hεM : ε * M ≤ ε * (M + 1) := by nlinarith
  linarith

/-- **INF18 O1. The annular neutral ground state.** For every large `N` there is `α_N > 2`
such that the completed neutral equation `F'' = (α_N² - W) F` has a Dirichlet solution on
`[-N, N]` (`neutralEvansFunction α_N (-N) N = 0`); it is the only Dirichlet wavenumber above
`1`; its normalized solution is real and positive on `(-N, N)`, so in particular nonzero at the
critical log-radius `t_* = log √8`.

`paper/main.tex` lines 1001--1011 (eq. st18-t00032, `α_{max,N} > 2`), with the uniqueness and
`N_*(t_*) ≠ 0` of bypass B8 (i) (scoping note `INF10-INF12-INF18-Planar.md` §4, B8; §5 O1);
blueprint units B0034 (annular threshold), B0028--B0029 (their Dirichlet analogue). -/
theorem exists_dirichlet_neutral : ∀ᶠ N : ℝ in atTop, ∃ αN : ℝ, 2 < αN ∧
    neutralEvansFunction αN (-N) N = 0 ∧
    (∀ β : ℝ, 1 < β → neutralEvansFunction β (-N) N = 0 → β = αN) ∧
    neutralNormalizedF αN (-N) neutralCriticalTime ≠ 0 ∧
    ∀ t ∈ Ioo (-N) N, 0 < (neutralNormalizedF αN (-N) t).re := by
  obtain ⟨R, hR, β₀, hβ₀2, hβ₀3, htrial⟩ := exists_trial_wavenumber
  filter_upwards [eventually_ge_atTop R, eventually_gt_atTop neutralCriticalTime] with N hNR hNt
  have hN0 : 0 < N := hR.trans_le hNR
  have ha : -N < neutralCriticalTime := by linarith [neutralCriticalTime_pos]
  obtain ⟨αN, hαI, hαD⟩ :=
    exists_neutral_dirichlet_of_not_pos (by linarith) hβ₀3 (htrial N hNR)
  have hα2 : 2 < αN := hβ₀2.trans_le hαI.1
  have hα1 : 1 < αN ^ 2 := by nlinarith
  have hpos := neutralU_pos_of_dirichlet hα1 hαD
  refine ⟨αN, hα2, (neutralEvansFunction_eq_zero_iff _ _ _).mpr hαD, ?_, ?_, hpos⟩
  · intro β hβ hD
    exact neutral_dirichlet_unique hβ (by linarith) (by linarith)
      ((neutralEvansFunction_eq_zero_iff _ _ _).mp hD) hαD
  · rw [neutralNormalizedF_ne_zero_iff]
    exact (hpos _ ⟨ha, hNt⟩).ne'

end UnforcedLeray.Rayleigh.Evans
