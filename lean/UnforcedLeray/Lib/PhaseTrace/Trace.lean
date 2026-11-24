import UnforcedLeray.Lib.PhaseTrace.Comoving

/-!
# The strong phase trace and its sup bound (INF14 T6, `phase_trace`; INF25 B25-4)

Tex 7389–7395 (`eq:free-stress-4`) and the proof at tex 7607–7632 (`sec:st18-9174`), unit
B0434: every `w` with `T₀w = b ∈ Y_q` has a strongly continuous `L^q` phase representative,
and

  `sup_τ ‖w(τ)‖_{L^q} ≤ (1 + 3P/(2q)) ‖w‖_{Y_q} + P ‖T₀w‖_{Y_q}`.

Following bypass B25-4 (scoping note `INF15-INF17-INF25-Parabolic.md`, decision D15 of
`scoping/README.md`; checked in `scoping/critic.md`), the norm chain rule is replaced by the
triangle inequality on the absolutely continuous chart path. With `V(t) = dil t (w(s + t))`,
`‖V(t)‖ = e^{3t/(2q)} ‖w(s + t)‖` and `V(t) - V(0) = ∫₀ᵗ V'`, so for `0 ≤ t ≤ P`

  `‖w(s + t)‖ ≤ e^{-3t/(2q)} ‖w(s)‖ + ∫₀ᵗ e^{3(r-t)/(2q)} ‖b(s + r)‖ dr
             ≤ ‖w(s)‖ + ∫₀ᴾ ‖b(s + r)‖ dr ≤ ‖w(s)‖ + P ‖b‖_{Y_q}`,

and choosing `s` with `‖w(s)‖ ≤ ‖w‖_{Y_q}` gives the bound with constant `1` in place of
`1 + 3P/(2q)` (`norm_phaseRep_le`).

Construction (`phaseRep`): for each base phase `s`, `chartRep s` is the continuous
representative on `[-(P+1), P+1]` of the comoving pullback (T1 `HasWeakDerivTime.rep`
applied to `comoving_hasWeakDerivTime`), and `phaseRep s = chartRep s 0`. Uniqueness of
continuous representatives gives `phaseRep (s + t) = dil (-t) (chartRep s t)` for
`|t| < P + 1` (`phaseRep_add`), hence continuity, periodicity, the a.e. identification with
`w`, and the bound.

Status: infrastructure (target T6, second half). Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.PhaseTrace

open UnforcedLeray.PhaseSpace UnforcedLeray.BochnerTime

/-- The representative of `HasWeakDerivTime` depends only on the two functions. -/
theorem rep_congr {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {a b : ℝ} {u v u' v' : ℝ → X} (hu : u = v) (hu' : u' = v')
    (h₁ : HasWeakDerivTime a b u u') (h₂ : HasWeakDerivTime a b v v') : h₁.rep = h₂.rep := by
  subst hu hu'
  rfl

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- A Haar-a.e. property on the circle holds for a.e. lift on the line. -/
theorem ae_comp_mk {p : AddCircle P → Prop} (hp : ∀ᵐ x ∂AddCircle.haarAddCircle, p x) :
    ∀ᵐ t : ℝ ∂volume, p (t : AddCircle P) := by
  have hp' : ∀ᵐ x ∂(volume : Measure (AddCircle P)), p x := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure hp _
  have h : ∀ k : ℤ, ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 + k • P) (0 + (k + 1) • P))),
      p (t : AddCircle P) := by
    intro k
    have hmp := AddCircle.measurePreserving_mk P (0 + k • P)
    have e : (0 + (k + 1) • P) = (0 + k • P) + P := by rw [add_smul, one_smul]; ring
    rw [e]
    exact hmp.quasiMeasurePreserving.ae hp'
  rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), ← iUnion_Ioc_add_zsmul hP.out 0,
    ae_restrict_iUnion_iff]
  exact h

section Rep

variable (hq : q ≠ ⊤) {w b : Yq P q} (h : HasPhaseOp driftT w b)

/-- The continuous representative of the comoving pullback based at `s`, on `[-(P+1), P+1]`. -/
def chartRep (s : ℝ) : ℝ → Lp CVec3 q (volume : Measure Space) :=
  (comoving_hasWeakDerivTime hq h s (-(P + 1)) (P + 1)).rep

/-- **The phase representative**: `phaseRep τ = chartRep τ 0`. -/
def phaseRep (τ : ℝ) : Lp CVec3 q (volume : Measure Space) := chartRep hq h τ 0

include hq h in
theorem chartRep_continuousOn (s : ℝ) :
    ContinuousOn (chartRep hq h s) (Icc (-(P + 1)) (P + 1)) :=
  HasWeakDerivTime.continuousOn_rep _

include hq h in
theorem chartRep_ae (s : ℝ) :
    comoving w s =ᵐ[volume.restrict (Ioo (-(P + 1)) (P + 1))] chartRep hq h s :=
  HasWeakDerivTime.ae_eq_rep _

include hq h in
theorem chartRep_sub (s : ℝ) {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc (-(P + 1)) (P + 1))
    (ht₂ : t₂ ∈ Icc (-(P + 1)) (P + 1)) :
    chartRep hq h s t₂ - chartRep hq h s t₁ = ∫ r in t₁..t₂, comoving b s r :=
  HasWeakDerivTime.rep_sub_rep _ ht₁ ht₂

theorem comoving_shift (f : Yq P q) (s t t' : ℝ) :
    comoving f (s + t) t' = dil CVec3 q (-t) (comoving f s (t' + t)) := by
  simp only [comoving, dil_dil]
  rw [show -t + (t' + t) = t' by ring, show s + (t' + t) = s + t + t' by ring]

include hq h in
/-- **Change of base point.** `phaseRep (s + t) = dil (-t) (chartRep s t)` for `|t| < P + 1`. -/
theorem phaseRep_add (s t : ℝ) (ht : |t| < P + 1) :
    phaseRep hq h (s + t) = dil CVec3 q (-t) (chartRep hq h s t) := by
  set L : ℝ := P + 1 with hLdef
  set J : Set ℝ := Ioo (max (-L) (-L - t)) (min L (L - t)) with hJdef
  rw [abs_lt] at ht
  have hJ0 : (0 : ℝ) ∈ J := by
    refine ⟨max_lt (by linarith) (by linarith), lt_min (by linarith) (by linarith)⟩
  have hJsub : J ⊆ Ioo (-L) L := fun x hx =>
    ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  have hJsub' : ∀ x ∈ J, x + t ∈ Ioo (-L) L := fun x hx => by
    have h1 := lt_of_le_of_lt (le_max_right _ _) hx.1
    have h2 := lt_of_lt_of_le hx.2 (min_le_right _ _)
    exact ⟨by linarith, by linarith⟩
  have h1 : ∀ᵐ x ∂volume, x ∈ Ioo (-L) L → comoving w (s + t) x = chartRep hq h (s + t) x :=
    (ae_restrict_iff' measurableSet_Ioo).mp (chartRep_ae hq h (s + t))
  have h2 : ∀ᵐ x ∂volume, x ∈ Ioo (-L) L → comoving w s x = chartRep hq h s x :=
    (ae_restrict_iff' measurableSet_Ioo).mp (chartRep_ae hq h s)
  have h2' : ∀ᵐ x ∂volume, x + t ∈ Ioo (-L) L →
      comoving w s (x + t) = chartRep hq h s (x + t) :=
    (measurePreserving_add_right volume t).quasiMeasurePreserving.ae h2
  have hae : chartRep hq h (s + t) =ᵐ[volume.restrict J]
      fun x => dil CVec3 q (-t) (chartRep hq h s (x + t)) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [h1, h2'] with x hx1 hx2 hxJ
    rw [← hx1 (hJsub hxJ), comoving_shift, hx2 (hJsub' x hxJ)]
  have hc1 : ContinuousOn (chartRep hq h (s + t)) J :=
    (chartRep_continuousOn hq h (s + t)).mono (hJsub.trans Ioo_subset_Icc_self)
  have hc2 : ContinuousOn (fun x => dil CVec3 q (-t) (chartRep hq h s (x + t))) J :=
    (dil CVec3 q (-t)).continuous.comp_continuousOn
      ((chartRep_continuousOn hq h s).comp (continuous_add_right t).continuousOn
        (fun x hx => Ioo_subset_Icc_self (hJsub' x hx)))
  have := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo hc1 hc2 hJ0
  simpa [phaseRep] using this

include hq h in
theorem continuous_phaseRep : Continuous (phaseRep hq h) := by
  rw [continuous_iff_continuousAt]
  intro τ₁
  have hL : (0 : ℝ) < P + 1 := by linarith [hP.out]
  have hev : (fun t => phaseRep hq h (τ₁ + t)) =ᶠ[𝓝 0]
      fun t => dil CVec3 q (-t) (chartRep hq h τ₁ t) := by
    have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-(P + 1)) (P + 1) :=
      Ioo_mem_nhds (by linarith) hL
    filter_upwards [hnear] with t ht
    exact phaseRep_add hq h τ₁ t (abs_lt.mpr ⟨ht.1, ht.2⟩)
  have hR : ContinuousAt (chartRep hq h τ₁) 0 :=
    (chartRep_continuousOn hq h τ₁).continuousAt (Icc_mem_nhds (by linarith) hL)
  have hpair : ContinuousAt
      (fun t : ℝ => ((-t, chartRep hq h τ₁ t) : ℝ × Lp CVec3 q (volume : Measure Space))) 0 :=
    continuous_neg.continuousAt.prodMk hR
  have hc : ContinuousAt ((fun p : ℝ × Lp CVec3 q (volume : Measure Space) =>
      dil CVec3 q p.1 p.2) ∘ (fun t : ℝ => ((-t, chartRep hq h τ₁ t) :
        ℝ × Lp CVec3 q (volume : Measure Space)))) 0 :=
    (continuous_dil hq).continuousAt.comp hpair
  have h1 : ContinuousAt (fun t => phaseRep hq h (τ₁ + t)) 0 := hc.congr hev.symm
  have h2 : ContinuousAt (fun τ : ℝ => τ - τ₁) τ₁ := (continuous_sub_right τ₁).continuousAt
  have h3 := ContinuousAt.comp_of_eq (g := fun t => phaseRep hq h (τ₁ + t)) h1 h2 (sub_self τ₁)
  have h4 : (fun t => phaseRep hq h (τ₁ + t)) ∘ (fun τ : ℝ => τ - τ₁) = phaseRep hq h := by
    funext τ
    simp only [Function.comp_apply]
    congr 1
    ring
  rw [h4] at h3
  exact h3

include hq h in
theorem phaseRep_periodic : Function.Periodic (phaseRep hq h) P := by
  intro τ
  show chartRep hq h (τ + P) 0 = chartRep hq h τ 0
  unfold chartRep
  exact congrFun (rep_congr (comoving_add_period w τ) (comoving_add_period b τ)
    (comoving_hasWeakDerivTime hq h (τ + P) (-(P + 1)) (P + 1))
    (comoving_hasWeakDerivTime hq h τ (-(P + 1)) (P + 1))) 0

include hq h in
theorem phaseRep_ae (s : ℝ) :
    ∀ᵐ t ∂(volume.restrict (Ioo (-(P + 1)) (P + 1))),
      phaseRep hq h (s + t) = w ((s + t : ℝ) : AddCircle P) := by
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp (chartRep_ae hq h s)] with t ht htI
  rw [phaseRep_add hq h s t (abs_lt.mpr ⟨htI.1, htI.2⟩), ← ht htI, comoving, dil_neg_dil]

/-- The phase representative descended to the circle. -/
def phaseRepC : C(AddCircle P, Lp CVec3 q (volume : Measure Space)) :=
  ⟨(phaseRep_periodic hq h).lift, continuous_coinduced_dom.mpr (continuous_phaseRep hq h)⟩

theorem phaseRepC_coe (τ : ℝ) : phaseRepC hq h (τ : AddCircle P) = phaseRep hq h τ := rfl

include hq h in
/-- `phaseRepC` represents `w`. -/
theorem phaseRepC_ae :
    (w : AddCircle P → Lp CVec3 q (volume : Measure Space)) =ᵐ[AddCircle.haarAddCircle]
      phaseRepC hq h := by
  refine (ae_eq_of_ae_eq_comp_mk (phaseRepC hq h).continuous w ?_).symm
  have h0 := phaseRep_ae hq h 0
  have hsub : Ioc (0 : ℝ) (0 + P) ⊆ Ioo (-(P + 1)) (P + 1) := fun x hx =>
    ⟨by linarith [hx.1, hP.out], by linarith [hx.2]⟩
  rw [ae_restrict_iff' measurableSet_Ioc]
  rw [ae_restrict_iff' measurableSet_Ioo] at h0
  filter_upwards [h0] with t ht htI
  have := ht (hsub htI)
  simp only [zero_add] at this
  rw [phaseRepC_coe, this]

include hq h in
/-- A phase at which the representative is no larger than `‖w‖_{Y_q}` (tex 7628). -/
theorem exists_phaseRep_le : ∃ s₀ : ℝ, ‖phaseRep hq h s₀‖ ≤ ‖w‖ := by
  have hq0 : 0 < q.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
  obtain ⟨x, hx⟩ := exists_le_lintegral (μ := AddCircle.haarAddCircle (T := P))
    (f := fun x => ‖phaseRepC hq h x‖ₑ ^ q.toReal)
    ((phaseRepC hq h).continuous.enorm.measurable.pow_const _).aemeasurable
  have hint : ∫⁻ x, ‖phaseRepC hq h x‖ₑ ^ q.toReal ∂AddCircle.haarAddCircle =
      ‖w‖ₑ ^ q.toReal := by
    rw [← lintegral_enorm_rpow_Yq w hq]
    refine lintegral_congr_ae ?_
    filter_upwards [phaseRepC_ae hq h] with x hx
    rw [hx]
  rw [hint] at hx
  have hx' : ‖phaseRepC hq h x‖ₑ ≤ ‖w‖ₑ := (ENNReal.rpow_le_rpow_iff hq0).mp hx
  obtain ⟨s₀, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨s₀, ?_⟩
  rw [← phaseRepC_coe hq h s₀]
  rw [← ofReal_norm, ← ofReal_norm] at hx'
  exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp hx'

include hq h in
/-- **Bypass B25-4 on one period**: for `0 ≤ t ≤ P`,
`‖w̃(s + t)‖ ≤ ‖w̃(s)‖ + P ‖b‖_{Y_q}`. -/
theorem norm_phaseRep_add_le (s : ℝ) {t : ℝ} (ht : t ∈ Icc 0 P) :
    ‖phaseRep hq h (s + t)‖ ≤ ‖phaseRep hq h s‖ + P * ‖b‖ := by
  have hP0 := hP.out
  have htL : |t| < P + 1 := by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
  have hIcc : ∀ x ∈ Icc (0 : ℝ) P, x ∈ Icc (-(P + 1)) (P + 1) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  set R := chartRep hq h s with hRdef
  have hR0 : R 0 = phaseRep hq h s := rfl
  have hsub := chartRep_sub hq h s (hIcc 0 ⟨le_rfl, hP0.le⟩) (hIcc t ht)
  have hRt : ‖R t‖ ≤ ‖R 0‖ +
      ∫ r in (0 : ℝ)..t, dilConst q r * ‖b ((s + r : ℝ) : AddCircle P)‖ := by
    have e1 : R t = R 0 + ∫ r in (0 : ℝ)..t, comoving b s r := by
      rw [← hsub]; abel
    rw [e1]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans (le_of_eq ?_)
    exact intervalIntegral.integral_congr fun r _ => norm_comoving b s r
  rw [phaseRep_add hq h s t htL, norm_dil]
  have hI : IntervalIntegrable (fun r => ‖b ((s + r : ℝ) : AddCircle P)‖) volume 0 t :=
    intervalIntegrable_norm_shift b s 0 t
  have hI' : IntervalIntegrable
      (fun r => dilConst q r * ‖b ((s + r : ℝ) : AddCircle P)‖) volume 0 t :=
    hI.continuousOn_mul (continuous_dilConst q).continuousOn
  have hdc : dilConst q (-t) ≤ 1 := dilConst_le_one q (by linarith [ht.1])
  have hdc0 : 0 ≤ dilConst q (-t) := (dilConst_pos q _).le
  have hmain : dilConst q (-t) *
      ∫ r in (0 : ℝ)..t, dilConst q r * ‖b ((s + r : ℝ) : AddCircle P)‖ ≤
        ∫ r in (0 : ℝ)..t, ‖b ((s + r : ℝ) : AddCircle P)‖ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on ht.1 (hI'.const_mul _) hI fun r hr => ?_
    rw [← mul_assoc, ← dilConst_add]
    have : dilConst q (-t + r) ≤ 1 := dilConst_le_one q (by linarith [hr.2])
    calc dilConst q (-t + r) * ‖b ((s + r : ℝ) : AddCircle P)‖
        ≤ 1 * ‖b ((s + r : ℝ) : AddCircle P)‖ := by gcongr
      _ = ‖b ((s + r : ℝ) : AddCircle P)‖ := one_mul _
  have hper : ∫ r in (0 : ℝ)..t, ‖b ((s + r : ℝ) : AddCircle P)‖ ≤ P * ‖b‖ := by
    calc ∫ r in (0 : ℝ)..t, ‖b ((s + r : ℝ) : AddCircle P)‖
        ≤ ∫ r in (0 : ℝ)..P, ‖b ((s + r : ℝ) : AddCircle P)‖ :=
          intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
            (Eventually.of_forall fun r => norm_nonneg _) (intervalIntegrable_norm_shift b s 0 P)
      _ = ∫ r in s..s + P, ‖b (r : AddCircle P)‖ := by
          rw [intervalIntegral.integral_comp_add_left (fun r => ‖b (r : AddCircle P)‖) s]
          simp
      _ ≤ P * ‖b‖ := intervalIntegral_norm_comp_mk_le b s
  have hRt' := mul_le_mul_of_nonneg_left hRt hdc0
  have hR0' : dilConst q (-t) * ‖R 0‖ ≤ ‖R 0‖ := by
    calc dilConst q (-t) * ‖R 0‖ ≤ 1 * ‖R 0‖ := by gcongr
      _ = ‖R 0‖ := one_mul _
  rw [mul_add] at hRt'
  rw [← hR0]
  linarith

include hq h in
/-- **The sup bound with constant one** (bypass B25-4): `‖w̃(τ)‖ ≤ ‖w‖_{Y_q} + P ‖b‖_{Y_q}`. -/
theorem norm_phaseRep_le (τ : ℝ) : ‖phaseRep hq h τ‖ ≤ ‖w‖ + P * ‖b‖ := by
  obtain ⟨s₀, hs₀⟩ := exists_phaseRep_le hq h
  have hP0 := hP.out
  set τ' := toIcoMod hP0 s₀ τ with hτ'def
  have hτ' : τ' ∈ Ico s₀ (s₀ + P) := toIcoMod_mem_Ico hP0 s₀ τ
  have heq : phaseRep hq h τ = phaseRep hq h τ' := by
    rw [hτ'def, toIcoMod]
    exact ((phaseRep_periodic hq h).sub_zsmul_eq _).symm
  rw [heq, show τ' = s₀ + (τ' - s₀) by ring]
  have := norm_phaseRep_add_le hq h s₀ (t := τ' - s₀) ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
  linarith

include hq h in
/-- The lift of the representative agrees with the lift of `w` for a.e. phase on the line. -/
theorem phaseRep_ae_line :
    ∀ᵐ τ : ℝ ∂volume, phaseRep hq h τ = w (τ : AddCircle P) := by
  filter_upwards [ae_comp_mk (phaseRepC_ae hq h)] with τ hτ
  rw [← phaseRepC_coe, hτ]

end Rep

end UnforcedLeray.PhaseTrace
