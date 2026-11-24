import UnforcedLeray.Units.B0447

/-!
# B0449, step 1: a Bochner weak time derivative is a space-time distributional derivative

Blueprint unit B0449 (`eq:free-stress-5`), manuscript `paper/main.tex` lines 7663–7681: the
cut-off chart `H = χW` satisfies `F = (∂_t − Δ_z + 1)H` **in distributions on space-time**,
where (20) (B0447, tex 7643–7649) gives `W_t = (T₀w) ∘ chart` only as the weak derivative of the
`L^q(ℝ³)`-valued map `t ↦ W(t)` (Bochner sense, tested against scalar functions of `t`).

This file proves the generic step from the Bochner form to the space-time form, for test
functions `θ(t, z)` that are not products: if `u' = v` weakly on `(a, b)` in `L^q(ℝ³)`, `U, V`
are jointly measurable representatives, and `θ` is `C¹` in `t` with bounded support inside
`(a, b) × ℝ³`, then `∫∫ ∂_tθ · U = −∫∫ θ · V` (`integral_dt_mul_eq`). The proof is the
fundamental theorem of calculus for the continuous representative (`HasWeakDerivTime.rep_eq`)
followed by Fubini on the triangle `a < r ≤ t`.

Auxiliary: `ballInd` (indicator of a closed ball), `lintegral_mul_le` (Hölder on a ball),
`integrable_mul_path` (space-time integrability of `g · U` for an `L¹_t L^q_z` path), `pairCLM`
(the pairing `f ↦ ∫ g f` as a continuous functional on `L^q`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace UnforcedLeray.BochnerTime

/-- Indicator of the closed ball `B̄(0, R) ⊂ ℝ³`. -/
def ballInd (R : ℝ) (z : Space) : ℝ :=
  (Metric.closedBall (0 : Space) R).indicator (fun _ => (1 : ℝ)) z

theorem ballInd_nonneg (R : ℝ) (z : Space) : 0 ≤ ballInd R z :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) z

theorem memLp_ballInd (R : ℝ) (r : ℝ≥0∞) : MemLp (ballInd R) r volume :=
  memLp_indicator_const r measurableSet_closedBall 1 (Or.inr measure_closedBall_lt_top.ne)

theorem ind_nonneg (s : Set ℝ) (t : ℝ) : 0 ≤ s.indicator (fun _ => (1 : ℝ)) t :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) t

theorem ind_le_one (s : Set ℝ) (t : ℝ) : s.indicator (fun _ => (1 : ℝ)) t ≤ 1 := by
  by_cases ht : t ∈ s <;> simp [ht]

theorem bound_le {M x y : ℝ} (hM : 0 ≤ M) (_hx0 : 0 ≤ x) (hx : x ≤ 1) (hy : 0 ≤ y) :
    M * x * y ≤ M * y := by
  nlinarith [mul_nonneg (mul_nonneg hM hy) (sub_nonneg.2 hx)]

/-- A measurable function bounded by `M · 1_{B̄(0,R)}` lies in every `L^r(ℝ³)`. -/
theorem memLp_of_le_ball {g : Space → ℂ} (hg : AEStronglyMeasurable g volume) {M R : ℝ}
    (hgb : ∀ z, ‖g z‖ ≤ M * ballInd R z) (r : ℝ≥0∞) : MemLp g r volume := by
  refine ((memLp_ballInd R r).const_mul M).of_le hg (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact (hgb z).trans (le_abs_self _)

/-- **Hölder on a ball**: `∫ |g f| ≤ M ‖1_{B̄(0,R)}‖_{q'} ‖f‖_q` for `|g| ≤ M 1_{B̄(0,R)}`. -/
theorem lintegral_mul_le {q : ℝ≥0∞} [Fact (1 ≤ q)] {g f : Space → ℂ}
    (hg : AEStronglyMeasurable g volume) (hf : AEStronglyMeasurable f volume) {M R : ℝ}
    (hM : 0 ≤ M) (hgb : ∀ z, ‖g z‖ ≤ M * ballInd R z) :
    ∫⁻ z, ‖g z * f z‖ₑ ≤
      ENNReal.ofReal M * eLpNorm (ballInd R) (conjExp q) volume * eLpNorm f q volume := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := (volume : Measure Space))
    (p := conjExp q) (q := q) (r := 1) hg hf (fun a b => a * b) 1
    (Eventually.of_forall fun z => by simp [nnnorm_mul])
  rw [eLpNorm_one_eq_lintegral_enorm, ENNReal.coe_one, one_mul] at h
  refine h.trans ?_
  gcongr
  calc eLpNorm g (conjExp q) volume ≤ eLpNorm (fun z => M * ballInd R z) (conjExp q) volume :=
        eLpNorm_mono_real (fun z => hgb z)
    _ = ENNReal.ofReal M * eLpNorm (ballInd R) (conjExp q) volume := by
        rw [show (fun z => M * ballInd R z) = M • ballInd R from rfl, eLpNorm_const_smul,
          Real.enorm_of_nonneg hM]

/-- **Space-time integrability.** If `U(t, ·) = u(t)` a.e. for `t ∈ J`, with
`u ∈ L¹(J; L^q(ℝ³))`, and `|g(t, z)| ≤ M 1_J(t) 1_{B̄(0,R)}(z)`, then `g · U ∈ L¹(ℝ × ℝ³)`. -/
theorem integrable_mul_path {q : ℝ≥0∞} [Fact (1 ≤ q)] {U : ℝ × Space → ℂ}
    (hU : StronglyMeasurable U) {u : ℝ → Lp ℂ q (volume : Measure Space)} {J : Set ℝ}
    (hJ : MeasurableSet J) (hu : IntegrableOn u J)
    (hUu : ∀ t ∈ J, (fun z => U (t, z)) =ᵐ[volume] u t)
    {g : ℝ × Space → ℂ} (hg : StronglyMeasurable g) {M R : ℝ} (hM : 0 ≤ M)
    (hgb : ∀ t z, ‖g (t, z)‖ ≤ M * J.indicator (fun _ => (1 : ℝ)) t * ballInd R z) :
    Integrable (fun p => g p * U p) volume := by
  refine ⟨(hg.mul hU).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, Measure.volume_eq_prod,
    lintegral_prod (fun p : ℝ × Space => ‖g p * U p‖ₑ) (hg.mul hU).measurable.enorm.aemeasurable]
  set C := ENNReal.ofReal M * eLpNorm (ballInd R) (conjExp q) volume with hCdef
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (memLp_ballInd R _).eLpNorm_ne_top
  have hle : ∀ t, ∫⁻ z, ‖g (t, z) * U (t, z)‖ₑ ≤ J.indicator (fun t => C * ‖u t‖ₑ) t := by
    intro t
    by_cases ht : t ∈ J
    · rw [indicator_of_mem ht]
      have h1 := lintegral_mul_le (q := q) (g := fun z => g (t, z)) (f := fun z => U (t, z))
        (hg.comp_measurable measurable_prodMk_left).aestronglyMeasurable
        (hU.comp_measurable measurable_prodMk_left).aestronglyMeasurable hM
        (fun z => by simpa [indicator_of_mem ht] using hgb t z)
      rw [eLpNorm_congr_ae (hUu t ht), ← Lp.enorm_def] at h1
      exact h1
    · rw [indicator_of_notMem ht]
      have h0 : ∀ z, g (t, z) = 0 := fun z =>
        norm_le_zero_iff.1 (by simpa [indicator_of_notMem ht] using hgb t z)
      simp [h0]
  calc ∫⁻ t, ∫⁻ z, ‖g (t, z) * U (t, z)‖ₑ ≤ ∫⁻ t, J.indicator (fun t => C * ‖u t‖ₑ) t :=
        lintegral_mono hle
    _ = C * ∫⁻ t in J, ‖u t‖ₑ := by rw [lintegral_indicator hJ, lintegral_const_mul' _ _ hC]
    _ < ∞ := ENNReal.mul_lt_top hC.lt_top hu.2

/-- The pairing `f ↦ ∫ g f` with `g ∈ L^{q'}`, as a continuous functional on `L^q(ℝ³)`. -/
def pairCLM {q : ℝ≥0∞} [Fact (1 ≤ q)] (g : Space → ℂ) (hg : MemLp g (conjExp q) volume) :
    Lp ℂ q (volume : Measure Space) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume (conjExp q) q (hg.toLp g)

theorem pairCLM_apply {q : ℝ≥0∞} [Fact (1 ≤ q)] (g : Space → ℂ)
    (hg : MemLp g (conjExp q) volume) (f : Lp ℂ q (volume : Measure Space)) :
    pairCLM g hg f = ∫ z, g z * (f : Space → ℂ) z := by
  rw [pairCLM, ContinuousLinearMap.lpPairing_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with z hz
  simp [hz]

set_option maxHeartbeats 1600000 in
/-- **Bochner weak derivative ⇒ space-time weak derivative** (tex 7663–7681, the step
"`F = (∂_t − Δ_z + 1)H` in distributions" for the time part). Let `v` be the weak derivative of
`u` on `(a, b)` in `L^q(ℝ³)`, with jointly measurable representatives `U, V`. Let `θ` be
continuous with `∂_tθ = θt` continuous, both bounded by `M 1_{[a',b']}(t) 1_{B̄(0,R)}(z)` with
`a < a'`, `b' < b`. Then `∫∫ θt · U = −∫∫ θ · V`. -/
theorem integral_dt_mul_eq {q : ℝ≥0∞} [Fact (1 ≤ q)] {a b : ℝ}
    {u v : ℝ → Lp ℂ q (volume : Measure Space)} (h : HasWeakDerivTime a b u v)
    {U V : ℝ × Space → ℂ} (hU : StronglyMeasurable U) (hV : StronglyMeasurable V)
    (hUu : ∀ t ∈ Ioo a b, (fun z => U (t, z)) =ᵐ[volume] u t)
    (hVv : ∀ t ∈ Ioo a b, (fun z => V (t, z)) =ᵐ[volume] v t)
    {θ θt : ℝ × Space → ℂ} (hθ : Continuous θ) (hθt : Continuous θt)
    (hd : ∀ t z, HasDerivAt (fun s => θ (s, z)) (θt (t, z)) t)
    {a' b' M R : ℝ} (ha : a < a') (hab' : a' ≤ b') (hb : b' < b) (hM : 0 ≤ M)
    (hθb : ∀ t z, ‖θ (t, z)‖ ≤ M * (Icc a' b').indicator (fun _ => (1 : ℝ)) t * ballInd R z)
    (hθtb : ∀ t z, ‖θt (t, z)‖ ≤ M * (Icc a' b').indicator (fun _ => (1 : ℝ)) t * ballInd R z) :
    ∫ p, θt p * U p = -∫ p, θ p * V p := by
  set J := Icc a' b' with hJdef
  have hJI : J ⊆ Ioo a b := fun t ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hJfin : volume J ≠ ∞ := measure_Icc_lt_top.ne
  have hθ0 : ∀ t z, t ∉ J → θ (t, z) = 0 := fun t z ht =>
    norm_le_zero_iff.1 (by simpa [indicator_of_notMem ht] using hθb t z)
  have hθt0 : ∀ t z, t ∉ J → θt (t, z) = 0 := fun t z ht =>
    norm_le_zero_iff.1 (by simpa [indicator_of_notMem ht] using hθtb t z)
  have hsl : ∀ t z, ‖θt (t, z)‖ ≤ M * ballInd R z := fun t z =>
    (hθtb t z).trans (bound_le hM (ind_nonneg _ _) (ind_le_one _ _) (ballInd_nonneg _ _))
  have hslice : ∀ t : ℝ, Continuous fun z : Space => (t, z) := fun t =>
    continuous_const.prodMk continuous_id
  have hmem : ∀ t, MemLp (fun z => θt (t, z)) (conjExp q) volume := fun t =>
    memLp_of_le_ball (hθt.comp (hslice t)).aestronglyMeasurable (hsl t) _
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ → Lp ℂ q (volume : Measure Space) →L[ℂ] ℂ,
      Λ = fun t => pairCLM _ (hmem t) := ⟨_, rfl⟩
  have hΛ : ∀ t f, Λ t f = ∫ z, θt (t, z) * (f : Space → ℂ) z := by
    intro t f
    rw [hΛdef]
    exact pairCLM_apply _ _ f
  have hΛ0 : ∀ t f, t ∉ J → Λ t f = 0 := by
    intro t f ht
    have hz : ∀ z, θt (t, z) = 0 := fun z => hθt0 t z ht
    rw [hΛ]
    simp [hz]
  -- Step A: Fubini and the continuous representative.
  have hint1 : Integrable (fun p => θt p * U p) volume :=
    integrable_mul_path hU measurableSet_Icc (h.int.mono_set hJI) (fun t ht => hUu t (hJI ht))
      hθt.stronglyMeasurable hM hθtb
  have stepA : ∫ p, θt p * U p = ∫ t, Λ t (h.rep t) := by
    rw [Measure.volume_eq_prod, integral_prod _ (by rw [← Measure.volume_eq_prod]; exact hint1)]
    refine integral_congr_ae ?_
    have hae := h.ae_eq_rep
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo] at hae
    filter_upwards [hae] with t ht
    by_cases htJ : t ∈ J
    · rw [hΛ]
      refine integral_congr_ae ?_
      filter_upwards [hUu t (hJI htJ)] with z hz
      rw [hz, ht (hJI htJ)]
    · have hz : ∀ z, θt (t, z) = 0 := fun z => hθt0 t z htJ
      rw [hΛ0 t _ htJ]
      simp [hz]
  -- Step B: the FTC for the representative.
  have hab : a < b := (ha.trans_le hab').trans hb
  have stepB : ∀ t, Λ t (h.rep t) = Λ t (h.rep a) + ∫ r in Ioc a t, Λ t (v r) := by
    intro t
    by_cases htJ : t ∈ J
    · have htI : t ∈ Icc a b := Ioo_subset_Icc_self (hJI htJ)
      have hI : IntervalIntegrable v volume a t :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le htI.1).2
          (h.int'.mono_set (Ioo_subset_Ioo_right htI.2))
      rw [h.rep_eq hab.le htI, map_add, ← (Λ t).intervalIntegral_comp_comm hI,
        intervalIntegral.integral_of_le htI.1]
    · have hz : ∀ f, Λ t f = 0 := fun f => hΛ0 t f htJ
      simp [hz]
  -- The fundamental theorem of calculus in `t` for the test.
  have hFTC : ∀ r z, ∫ t in Ioi r, θt (t, z) = -θ (r, z) := by
    intro r z
    have hcs : HasCompactSupport (fun t => θt (t, z)) :=
      HasCompactSupport.intro isCompact_Icc (fun t ht => hθt0 t z ht)
    have hint : Integrable (fun t => θt (t, z)) :=
      (hθt.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport hcs
    have hlim : Tendsto (fun s => θ (s, z)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop b'] with s hs
      exact (hθ0 s z (fun hJ => absurd hJ.2 (not_le.2 hs))).symm
    have := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun s => θ (s, z))
      (f' := fun t => θt (t, z)) (hd r z).continuousAt.continuousWithinAt
      (fun x _ => hd x z) hint.integrableOn hlim
    rw [this, zero_sub]
  -- Step C: the constant part integrates to zero.
  have hint0 : Integrable (fun p : ℝ × Space => θt p * (h.rep a : Space → ℂ) p.2) volume :=
    integrable_mul_path (U := fun p => (h.rep a : Space → ℂ) p.2) (u := fun _ => h.rep a)
      ((Lp.stronglyMeasurable (h.rep a)).comp_measurable measurable_snd) measurableSet_Icc
      (integrableOn_const (hs := hJfin)) (fun t _ => Eventually.of_forall fun _ => rfl)
      hθt.stronglyMeasurable hM hθtb
  have hint0' : Integrable (fun p : ℝ × Space => θt p * (h.rep a : Space → ℂ) p.2)
      ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    rw [← Measure.volume_eq_prod]; exact hint0
  have h0 : ∀ z, ∫ t, θt (t, z) = 0 := by
    intro z
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi a)
      (fun t ht => hθt0 t z (fun hJ => ht (ha.trans_le hJ.1))), hFTC a z,
      hθ0 a z (fun hJ => absurd hJ.1 (not_le.2 ha)), neg_zero]
  have stepC : ∫ t, Λ t (h.rep a) = 0 := by
    simp_rw [hΛ]
    have hsw := integral_integral_swap (f := fun t z => θt (t, z) * (h.rep a : Space → ℂ) z)
      (μ := volume) (ν := volume) hint0'
    rw [hsw]
    simp only [integral_mul_const, h0, zero_mul, integral_zero]
  have hintΛ0 : Integrable (fun t => Λ t (h.rep a)) volume :=
    hint0'.integral_prod_left.congr (Eventually.of_forall fun t => (hΛ t (h.rep a)).symm)
  -- Step D: Fubini on the triangle `a < r ≤ t`.
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ → ℝ → ℂ, Φ = fun t r => ∫ z, θt (t, z) * V (r, z) := ⟨_, rfl⟩
  have hΦapp : ∀ t r, Φ t r = ∫ z, θt (t, z) * V (r, z) := fun t r => by rw [hΦdef]
  have hΦv : ∀ t, ∀ r ∈ Ioo a b, Λ t (v r) = Φ t r := by
    intro t r hr
    rw [hΛ, hΦapp]
    refine integral_congr_ae ?_
    filter_upwards [hVv r hr] with z hz
    rw [hz]
  have hΦ0 : ∀ t r, t ∉ J → Φ t r = 0 := by
    intro t r ht
    have hz : ∀ z, θt (t, z) = 0 := fun z => hθt0 t z ht
    rw [hΦapp]
    simp [hz]
  obtain ⟨S, hSdef⟩ : ∃ S : Set (ℝ × ℝ), S = {x | a < x.2 ∧ x.2 ≤ x.1} := ⟨_, rfl⟩
  have hSmem : ∀ t r, (t, r) ∈ S ↔ (a < r ∧ r ≤ t) := fun t r => by rw [hSdef]; rfl
  have hS : MeasurableSet S := by
    rw [hSdef]
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : ℝ × ℝ → ℂ, Ψ = S.indicator (Function.uncurry Φ) := ⟨_, rfl⟩
  have hΦm : StronglyMeasurable (Function.uncurry Φ) := by
    have h1 : StronglyMeasurable
        (fun x : (ℝ × ℝ) × Space => θt (x.1.1, x.2) * V (x.1.2, x.2)) :=
      (hθt.stronglyMeasurable.comp_measurable (measurable_fst.fst.prodMk measurable_snd)).mul
        (hV.comp_measurable (measurable_fst.snd.prodMk measurable_snd))
    rw [hΦdef]
    exact h1.integral_prod_right'
  obtain ⟨cB, hcB⟩ : ∃ cB : ℝ, cB = (eLpNorm (ballInd R) (conjExp q) volume).toReal := ⟨_, rfl⟩
  have hcB0 : 0 ≤ cB := by rw [hcB]; exact ENNReal.toReal_nonneg
  have hfin : eLpNorm (ballInd R) (conjExp q) volume ≠ ∞ := (memLp_ballInd R _).eLpNorm_ne_top
  have hΦb : ∀ t, ∀ r ∈ Ioo a b, ‖Φ t r‖ ≤ M * cB * ‖v r‖ := by
    intro t r hr
    have h1 : ‖Φ t r‖ₑ ≤ ENNReal.ofReal M * eLpNorm (ballInd R) (conjExp q) volume * ‖v r‖ₑ := by
      rw [hΦapp]
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      have h2 := lintegral_mul_le (q := q) (g := fun z => θt (t, z)) (f := fun z => V (r, z))
        (hθt.comp (hslice t)).aestronglyMeasurable
        (hV.comp_measurable measurable_prodMk_left).aestronglyMeasurable hM (hsl t)
      rwa [eLpNorm_congr_ae (hVv r hr), ← Lp.enorm_def] at h2
    have h3 := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) enorm_ne_top) h1
    rwa [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM,
      toReal_enorm, ← hcB] at h3
  have stepD1 : ∀ t, ∫ r in Ioc a t, Λ t (v r) = ∫ r, Ψ (t, r) := by
    intro t
    have e1 : ∫ r in Ioc a t, Λ t (v r) = ∫ r in Ioc a t, Φ t r := by
      by_cases htJ : t ∈ J
      · exact setIntegral_congr_fun measurableSet_Ioc
          (fun r hr => hΦv t r ⟨hr.1, hr.2.trans_lt (hJI htJ).2⟩)
      · have hz : ∀ f, Λ t f = 0 := fun f => hΛ0 t f htJ
        have hz' : ∀ r, Φ t r = 0 := fun r => hΦ0 t r htJ
        simp [hz, hz']
    rw [e1, ← integral_indicator measurableSet_Ioc]
    congr 1
    funext r
    rw [hΨdef]
    by_cases hr : r ∈ Ioc a t
    · rw [indicator_of_mem hr, indicator_of_mem ((hSmem t r).2 hr), Function.uncurry_apply_pair]
    · rw [indicator_of_notMem hr, indicator_of_notMem (fun h' => hr ((hSmem t r).1 h'))]
  have hnn : ∀ t r, 0 ≤ J.indicator (fun _ => (1 : ℝ)) t *
      (Ioo a b).indicator (fun r => M * cB * ‖v r‖) r := fun t r =>
    mul_nonneg (ind_nonneg _ _) (indicator_nonneg (fun r _ =>
      mul_nonneg (mul_nonneg hM hcB0) (norm_nonneg _)) _)
  have hΨint : Integrable Ψ ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have hdom : Integrable (fun x : ℝ × ℝ => J.indicator (fun _ => (1 : ℝ)) x.1 *
        (Ioo a b).indicator (fun r => M * cB * ‖v r‖) x.2)
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
      refine Integrable.mul_prod ?_ ?_
      · exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (hs := hJfin))
      · exact (integrable_indicator_iff measurableSet_Ioo).2 (h.int'.norm.const_mul (M * cB))
    have hΨm : StronglyMeasurable Ψ := by rw [hΨdef]; exact hΦm.indicator hS
    refine hdom.mono' hΨm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    obtain ⟨t, r⟩ := x
    by_cases hx : (t, r) ∈ S
    · rw [hΨdef, indicator_of_mem hx, Function.uncurry_apply_pair]
      by_cases htJ : t ∈ J
      · have hx' := (hSmem t r).1 hx
        have hr : r ∈ Ioo a b := ⟨hx'.1, hx'.2.trans_lt (hJI htJ).2⟩
        rw [indicator_of_mem htJ, indicator_of_mem hr, one_mul]
        exact hΦb t r hr
      · rw [hΦ0 t r htJ, norm_zero]
        exact hnn t r
    · rw [hΨdef, indicator_of_notMem hx, norm_zero]
      exact hnn t r
  have stepD4 : ∀ r, ∫ t, Ψ (t, r) = -∫ z, θ (r, z) * V (r, z) := by
    intro r
    by_cases hr : r ∈ Ioc a b'
    · have hrI : r ∈ Ioo a b := ⟨hr.1, hr.2.trans_lt hb⟩
      obtain ⟨gr, hgr⟩ : ∃ gr : ℝ × Space → ℂ,
          gr = fun p => (Ici r).indicator (fun _ => (1 : ℂ)) p.1 * θt p := ⟨_, rfl⟩
      have hgrapp : ∀ t z, gr (t, z) = (Ici r).indicator (fun _ => (1 : ℂ)) t * θt (t, z) :=
        fun t z => by rw [hgr]
      have hgrm : StronglyMeasurable gr := by
        rw [hgr]
        exact ((stronglyMeasurable_const.indicator measurableSet_Ici).comp_measurable
          measurable_fst).mul hθt.stronglyMeasurable
      have hgrb : ∀ t z, ‖gr (t, z)‖ ≤ M * J.indicator (fun _ => (1 : ℝ)) t * ballInd R z := by
        intro t z
        refine le_trans ?_ (hθtb t z)
        rw [hgrapp, norm_mul]
        by_cases ht : t ∈ Ici r
        · rw [indicator_of_mem ht, norm_one, one_mul]
        · rw [indicator_of_notMem ht, norm_zero, zero_mul]
          exact norm_nonneg _
      have hint2 : Integrable (fun p => gr p * V (r, p.2)) volume :=
        integrable_mul_path (U := fun p => V (r, p.2)) (u := fun _ => v r)
          (hV.comp_measurable (measurable_const.prodMk measurable_snd)) measurableSet_Icc
          (integrableOn_const (hs := hJfin)) (fun t _ => hVv r hrI) hgrm hM hgrb
      have hint2' : Integrable (fun p => gr p * V (r, p.2))
          ((volume : Measure ℝ).prod (volume : Measure Space)) := by
        rw [← Measure.volume_eq_prod]; exact hint2
      have e1 : ∀ t, Ψ (t, r) = ∫ z, gr (t, z) * V (r, z) := by
        intro t
        by_cases ht : r ≤ t
        · have hx : (t, r) ∈ S := (hSmem t r).2 ⟨hr.1, ht⟩
          have hti : t ∈ Ici r := ht
          rw [hΨdef, indicator_of_mem hx, Function.uncurry_apply_pair, hΦapp]
          simp only [hgrapp, indicator_of_mem hti, one_mul]
        · have hx : (t, r) ∉ S := fun hx => ht ((hSmem t r).1 hx).2
          have hti : t ∉ Ici r := ht
          rw [hΨdef, indicator_of_notMem hx]
          simp only [hgrapp, indicator_of_notMem hti, zero_mul, integral_zero]
      simp_rw [e1]
      have hsw := integral_integral_swap (f := fun t z => gr (t, z) * V (r, z))
        (μ := volume) (ν := volume) hint2'
      rw [hsw]
      have e2 : ∀ z, ∫ t, gr (t, z) * V (r, z) = -(θ (r, z) * V (r, z)) := by
        intro z
        rw [integral_mul_const]
        have e3 : ∫ t, gr (t, z) = ∫ t in Ici r, θt (t, z) := by
          rw [← integral_indicator measurableSet_Ici]
          congr 1
          funext t
          rw [hgrapp]
          by_cases ht : t ∈ Ici r
          · rw [indicator_of_mem ht, indicator_of_mem ht, one_mul]
          · rw [indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]
        rw [e3, integral_Ici_eq_integral_Ioi, hFTC r z, neg_mul]
      simp_rw [e2, integral_neg]
    · have hθr : ∀ z, θ (r, z) = 0 := fun z =>
        hθ0 r z (fun hJ => hr ⟨ha.trans_le hJ.1, hJ.2⟩)
      have hΨr : ∀ t, Ψ (t, r) = 0 := by
        intro t
        by_cases hx : (t, r) ∈ S
        · rw [hΨdef, indicator_of_mem hx, Function.uncurry_apply_pair]
          have hx' := (hSmem t r).1 hx
          have htJ : t ∉ J := fun htJ => hr ⟨hx'.1, hx'.2.trans htJ.2⟩
          exact hΦ0 t r htJ
        · rw [hΨdef, indicator_of_notMem hx]
      simp [hΨr, hθr]
  -- Step E: back to the space-time integral of `θ V`.
  have hint3 : Integrable (fun p => θ p * V p) volume :=
    integrable_mul_path hV measurableSet_Icc (h.int'.mono_set hJI) (fun t ht => hVv t (hJI ht))
      hθ.stronglyMeasurable hM hθb
  have stepE : ∫ p, θ p * V p = ∫ r, ∫ z, θ (r, z) * V (r, z) := by
    rw [Measure.volume_eq_prod, integral_prod _ (by rw [← Measure.volume_eq_prod]; exact hint3)]
  have hintQ : Integrable (fun t => ∫ r, Ψ (t, r)) volume := hΨint.integral_prod_left
  calc ∫ p, θt p * U p = ∫ t, Λ t (h.rep t) := stepA
    _ = ∫ t, (Λ t (h.rep a) + ∫ r, Ψ (t, r)) := by
        congr 1
        funext t
        rw [stepB t, stepD1 t]
    _ = (∫ t, Λ t (h.rep a)) + ∫ t, ∫ r, Ψ (t, r) := integral_add hintΛ0 hintQ
    _ = ∫ r, ∫ t, Ψ (t, r) := by
        rw [stepC, zero_add]
        exact integral_integral_swap (f := fun t r => Ψ (t, r)) hΨint
    _ = ∫ r, -∫ z, θ (r, z) * V (r, z) := by
        congr 1
        funext r
        exact stepD4 r
    _ = -∫ p, θ p * V p := by rw [integral_neg, stepE]

end UnforcedLeray.B0449
