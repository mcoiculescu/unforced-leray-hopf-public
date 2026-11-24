import UnforcedLeray.Units.B0062
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# B0063 helper: strong continuity of the transport group on `H^j_M`

Helper file of blueprint unit **B0063** (`paper/main.tex` lines 1238–1243): "Density of compact
smooth functions proves strong continuity." The group `T(t)f = f ∘ Φ_t` and its bound


**Proof used here.** Instead of a density theorem for `H^j_M` (not available in the library),
we use the iterated chain rule of B0062: `∂^α(T(t)f) = ∑_p c_p(t, ·) (∂^{γ_p} f) ∘ Φ_t`
(`der_transportFun_ae`). Each term converges in `L²(⟨y⟩^{2M}dy)` as `t → 0`:
* `g ∘ Φ_t → g` for every `g ∈ L²(⟨y⟩^{2M})`: Mathlib's continuity of
  `(g, Φ) ↦ g ∘ Φ` for measure-preserving continuous `Φ`
  (`Filter.Tendsto.compMeasurePreservingLp`, itself proved by density of simple functions —
  this is where density enters), applied to the continuous curve `t ↦ Φ_t` in `C(ℂ, ℂ)`;
* `c_p(t, ·) → c_p(0, ·)` pointwise with a uniform bound, so `(c_p(t) - c_p(0)) g → 0` by
  dominated convergence. The coefficients are jointly smooth in `(t, y)` (`terms_jSmooth`).

Main results: `contDiff_flow_uncurry`, `terms_jSmooth`, `tendsto_eLpNorm_comp_flow_sub`,
`tendsto_transport_zero` (`T(t)f → f` in `H^j_M`), `continuous_transport_apply`
(strong continuity at every time, by the group law).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff ENNReal NNReal Topology
open Set Filter MeasureTheory NonUniqueEuler.Sob UnforcedLeray.B0008 UnforcedLeray.B0062

namespace UnforcedLeray.B0063

/-! ### Joint smoothness of the flow and of the chain-rule coefficients -/

theorem contDiff_Omega_norm : ContDiff ℝ ∞ (fun y : ℂ => Omega ‖y‖) := by
  have h : (fun y : ℂ => Omega ‖y‖) = fun y : ℂ => Real.exp (-(‖y‖ ^ 2 / 4)) := rfl
  rw [h]
  exact Real.contDiff_exp.comp ((contDiff_norm_sq ℝ).div_const 4).neg

/-- The flow `(t, y) ↦ Φ_t(y) = e^{-iΩ(|y|)t} y` is jointly smooth. -/
theorem contDiff_flow_uncurry : ContDiff ℝ ∞ (fun p : ℝ × ℂ => flow p.1 p.2) := by
  have h : (fun p : ℝ × ℂ => flow p.1 p.2) =
      fun p : ℝ × ℂ => gexp (-(Omega ‖p.2‖ * p.1)) * p.2 := rfl
  rw [h]
  exact (contDiff_gexp.comp ((contDiff_Omega_norm.comp contDiff_snd).mul contDiff_fst).neg).mul
    contDiff_snd

/-- A coefficient family `c(t, y)` that is jointly smooth in `(t, y)`. -/
def JSmooth (c : Coef) : Prop := ContDiff ℝ ∞ (fun p : ℝ × ℂ => c p.1 p.2)

theorem JSmooth.const (a : ℂ) : JSmooth (fun _ _ => a) := contDiff_const

theorem JSmooth.mul {a b : Coef} (ha : JSmooth a) (hb : JSmooth b) :
    JSmooth (fun t y => a t y * b t y) := ContDiff.mul ha hb

theorem JSmooth.continuous_right {c : Coef} (hc : JSmooth c) (t : ℝ) : Continuous (c t) :=
  hc.continuous.comp (continuous_const.prodMk continuous_id)

theorem JSmooth.tendsto {c : Coef} (hc : JSmooth c) (y : ℂ) (t₀ : ℝ) :
    Tendsto (fun t => c t y) (𝓝 t₀) (𝓝 (c t₀ y)) :=
  (hc.continuous.comp (continuous_id.prodMk continuous_const)).tendsto t₀

/-- `(t, y) ↦ D_y c(t, y) v` is jointly smooth when `c` is. -/
theorem contDiff_fderiv_uncurry {c : ℝ → ℂ → ℂ}
    (hc : ContDiff ℝ ∞ (fun p : ℝ × ℂ => c p.1 p.2)) (v : ℂ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => fderiv ℝ (c p.1) p.2 v) := by
  have hu : ContDiff ℝ ∞ (Function.uncurry fun (p : ℝ × ℂ) (z : ℂ) => c p.1 z) :=
    hc.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact (ContDiff.fderiv hu contDiff_snd (by simp)).clm_apply contDiff_const

theorem JSmooth.dirDeriv {c : Coef} (hc : JSmooth c) (v : ℂ) :
    JSmooth (fun t y => dirDeriv v (c t) y) :=
  contDiff_fderiv_uncurry hc v

theorem contDiff_fderiv_flow_uncurry (v : ℂ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => fderiv ℝ (flow p.1) p.2 v) :=
  contDiff_fderiv_uncurry contDiff_flow_uncurry v

theorem jSmooth_bRe (v : ℂ) : JSmooth (bRe v) :=
  Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp (contDiff_fderiv_flow_uncurry v))

theorem jSmooth_bIm (v : ℂ) : JSmooth (bIm v) :=
  Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp (contDiff_fderiv_flow_uncurry v))

/-- The chain-rule coefficients of B0062 are jointly smooth in `(t, y)`. -/
theorem terms_jSmooth : ∀ (vs : List ℂ), ∀ p ∈ terms vs, JSmooth p.1
  | [] => by
    intro p hp
    simp only [terms, List.mem_singleton] at hp
    subst hp
    exact JSmooth.const 1
  | v :: vs => by
    intro p hp
    simp only [terms, List.mem_flatMap] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    have h := terms_jSmooth vs q hq
    simp only [step, List.mem_cons, List.not_mem_nil, or_false] at hpq
    rcases hpq with rfl | rfl | rfl
    · exact h.dirDeriv v
    · exact h.mul (jSmooth_bRe v)
    · exact h.mul (jSmooth_bIm v)

/-- The coefficients are jointly smooth and bounded uniformly for `|t| ≤ 1`. -/
theorem terms_good (vs : List ℂ) :
    ∀ p ∈ terms vs, JSmooth p.1 ∧ ∃ K : ℝ, ∀ t y, |t| ≤ 1 → ‖p.1 t y‖ ≤ K := by
  intro p hp
  refine ⟨terms_jSmooth vs p hp, ?_⟩
  obtain ⟨K, hK, hb⟩ := (terms_spec vs p hp).2.norm_le
  refine ⟨K * 2 ^ vs.length, fun t y ht => (hb t y).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) hK
  linarith

/-! ### Continuity of `g ↦ g ∘ Φ_t` in `L²(⟨y⟩^{2M} dy)` -/

/-- The flow map `Φ_t` as a continuous map. -/
def flowC (t : ℝ) : C(ℂ, ℂ) := ⟨flow t, (contDiff_flow t).continuous⟩

/-- `t ↦ Φ_t` is continuous into `C(ℂ, ℂ)` (compact-open topology). -/
theorem continuous_flowC : Continuous flowC := by
  let J : C(ℝ × ℂ, ℂ) := ⟨fun p => flow p.1 p.2, contDiff_flow_uncurry.continuous⟩
  have h : flowC = fun t => J.curry t := by
    funext t
    ext y
    rfl
  rw [h]
  exact J.curry.continuous

/-- `‖g ∘ Φ_t - g‖_{L²(⟨y⟩^{2M})} → 0` as `t → 0`. -/
theorem tendsto_eLpNorm_comp_flow_sub {M : ℝ} {g : ℂ → ℂ} (hg : MemLp g 2 (wMeasure M)) :
    Tendsto (fun t => eLpNorm (fun y => g (flow t y) - g y) 2 (wMeasure M)) (𝓝 0) (𝓝 0) := by
  have hmp : ∀ t, MeasurePreserving (flowC t) (wMeasure M) (wMeasure M) :=
    fun t => measurePreserving_flow_wMeasure M t
  have h := (tendsto_const_nhds (x := hg.toLp g)).compMeasurePreservingLp
    (continuous_flowC.tendsto 0) hmp (hmp 0) ENNReal.ofNat_ne_top
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h
  refine h.congr' (Eventually.of_forall fun t => eLpNorm_congr_ae ?_)
  have h1 := Lp.coeFn_compMeasurePreserving (hg.toLp g) (hmp t)
  have h2 := Lp.coeFn_compMeasurePreserving (hg.toLp g) (hmp 0)
  have h4 := (hmp t).quasiMeasurePreserving.ae_eq_comp hg.coeFn_toLp
  have h5 := (hmp 0).quasiMeasurePreserving.ae_eq_comp hg.coeFn_toLp
  filter_upwards [h1, h2, h4, h5] with y e1 e2 e4 e5
  rw [Pi.sub_apply, e1, e2, e4, e5]
  simp only [Function.comp_apply, flowC, ContinuousMap.coe_mk, flow_zero]

/-- Dominated convergence in `L²`: if `c(t, y) → 0` pointwise with a uniform bound, then
`‖c(t) g‖_{L²(μ)} → 0`. -/
theorem tendsto_eLpNorm_mul_of_tendsto {μ : Measure ℂ} {g : ℂ → ℂ} (hg : MemLp g 2 μ)
    {c : ℝ → ℂ → ℂ} {K : ℝ} (hcm : ∀ t, AEStronglyMeasurable (c t) μ)
    (hb : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y, ‖c t y‖ ≤ K)
    (hlim : ∀ y, Tendsto (fun t => c t y) (𝓝 0) (𝓝 0)) :
    Tendsto (fun t => eLpNorm (fun y => c t y * g y) 2 μ) (𝓝 0) (𝓝 0) := by
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
  have hpt : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have hL : Tendsto (fun t => ∫⁻ y, ‖c t y * g y‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) (𝓝 0)
      (𝓝 (∫⁻ _y, 0 ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence'
      (fun y => (ENNReal.ofReal K * ‖g y‖ₑ) ^ (2 : ℝ≥0∞).toReal) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun t => ((hcm t).mul hg.1).enorm.pow_const _
    · filter_upwards [hb] with t ht
      refine Eventually.of_forall fun y => ENNReal.rpow_le_rpow ?_ ENNReal.toReal_nonneg
      rw [enorm_mul]
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (ht y)
    · simp_rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
      rw [lintegral_const_mul' _ _
        (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)]
      exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)
        (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpt hg.2).ne
    · refine Eventually.of_forall fun y => ?_
      have h1 : Tendsto (fun t => c t y * g y) (𝓝 0) (𝓝 0) := by
        simpa using (hlim y).mul_const (g y)
      have h2 := (continuous_enorm.tendsto (0 : ℂ)).comp h1
      rw [enorm_zero] at h2
      have h3 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ≥0∞).toReal)).tendsto 0).comp h2
      have h4 : (0 : ℝ≥0∞) ^ (2 : ℝ≥0∞).toReal = 0 := ENNReal.zero_rpow_of_pos (by simp)
      rw [h4] at h3
      exact h3
  rw [lintegral_zero] at hL
  have h5 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0).comp hL
  have h6 : (0 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞).toReal) = 0 := ENNReal.zero_rpow_of_pos (by simp)
  rw [h6] at h5
  exact h5

/-- One term of the chain rule: `c(t) (g ∘ Φ_t) → c(0) g` in `L²(⟨y⟩^{2M})`. -/
theorem tendsto_term {M : ℝ} {g : ℂ → ℂ} (hg : MemLp g 2 (wMeasure M)) {c : Coef}
    (hc : JSmooth c) {K : ℝ} (hK : ∀ t y, |t| ≤ 1 → ‖c t y‖ ≤ K) :
    Tendsto (fun t => eLpNorm (fun y => c t y * g (flow t y) - c 0 y * g (flow 0 y)) 2
      (wMeasure M)) (𝓝 0) (𝓝 0) := by
  simp only [flow_zero]
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), |t| ≤ 1 := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
    simpa [Real.dist_eq] using ht
  have hgt : ∀ t, AEStronglyMeasurable (fun y => g (flow t y)) (wMeasure M) :=
    fun t => hg.1.comp_measurePreserving (measurePreserving_flow_wMeasure M t)
  have hA : Tendsto (fun t => ENNReal.ofReal K *
      eLpNorm (fun y => g (flow t y) - g y) 2 (wMeasure M)) (𝓝 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (tendsto_eLpNorm_comp_flow_sub hg)
      (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal K)
    simpa using this
  have hB : Tendsto (fun t => eLpNorm (fun y => (c t y - c 0 y) * g y) 2 (wMeasure M)) (𝓝 0)
      (𝓝 0) := by
    refine tendsto_eLpNorm_mul_of_tendsto hg (K := 2 * K)
      (fun t => ((hc.continuous_right t).sub (hc.continuous_right 0)).aestronglyMeasurable) ?_ ?_
    · filter_upwards [hnear] with t ht y
      calc ‖c t y - c 0 y‖ ≤ ‖c t y‖ + ‖c 0 y‖ := norm_sub_le _ _
        _ ≤ K + K := add_le_add (hK t y ht) (hK 0 y (by simp))
        _ = 2 * K := by ring
    · intro y
      have := (hc.tendsto y 0).sub_const (c 0 y)
      simpa using this
  have hsum := hA.add hB
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hnear] with t ht
  have e : (fun y => c t y * g (flow t y) - c 0 y * g y) =
      (fun y => c t y * (g (flow t y) - g y)) + (fun y => (c t y - c 0 y) * g y) := by
    funext y
    simp only [Pi.add_apply]
    ring
  rw [e]
  refine (eLpNorm_add_le ?_ ?_ (by norm_num)).trans (add_le_add ?_ le_rfl)
  · exact (hc.continuous_right t).aestronglyMeasurable.mul ((hgt t).sub hg.1)
  · exact ((hc.continuous_right t).sub (hc.continuous_right 0)).aestronglyMeasurable.mul hg.1
  · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun y => ?_) 2
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hK t y ht) (norm_nonneg _)

/-! ### Strong continuity -/

variable {j : ℕ} {M : ℝ}

theorem aestronglyMeasurable_termSum (F : HjM j M) (t : ℝ) :
    ∀ L : List (Coef × (ℕ × ℕ)), (∀ p ∈ L, Continuous (p.1 t)) →
      AEStronglyMeasurable (termSum F t L) (wMeasure M)
  | [], _ => by
    rw [termSum_nil]
    exact (continuous_const (y := (0 : ℂ))).aestronglyMeasurable
  | p :: L, hL => by
    rw [termSum_cons]
    exact ((hL p List.mem_cons_self).aestronglyMeasurable.mul (memLp_fam_comp F p.2 t).1).add
      (aestronglyMeasurable_termSum F t L fun q hq => hL q (List.mem_cons_of_mem _ hq))

theorem tendsto_termSum (F : HjM j M) :
    ∀ L : List (Coef × (ℕ × ℕ)),
      (∀ p ∈ L, JSmooth p.1 ∧ ∃ K : ℝ, ∀ t y, |t| ≤ 1 → ‖p.1 t y‖ ≤ K) →
      Tendsto (fun t => eLpNorm (termSum F t L - termSum F 0 L) 2 (wMeasure M)) (𝓝 0) (𝓝 0)
  | [], _ => by simp [termSum_nil]
  | p :: L, hL => by
    obtain ⟨hp, K, hK⟩ := hL p List.mem_cons_self
    have hL' : ∀ q ∈ L, JSmooth q.1 ∧ ∃ K : ℝ, ∀ t y, |t| ≤ 1 → ‖q.1 t y‖ ≤ K :=
      fun q hq => hL q (List.mem_cons_of_mem _ hq)
    have ih := tendsto_termSum F L hL'
    have h1 := tendsto_term (memLp_fam F p.2) hp hK
    have hs := h1.add ih
    rw [add_zero] at hs
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
      (fun _ => zero_le) fun t => ?_
    have e : termSum F t (p :: L) - termSum F 0 (p :: L) =
        (fun y => p.1 t y * fam F p.2 (flow t y) - p.1 0 y * fam F p.2 (flow 0 y)) +
          (termSum F t L - termSum F 0 L) := by
      rw [termSum_cons, termSum_cons]
      funext y
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [e]
    refine eLpNorm_add_le ?_ ?_ (by norm_num)
    · exact ((hp.continuous_right t).aestronglyMeasurable.mul (memLp_fam_comp F p.2 t).1).sub
        ((hp.continuous_right 0).aestronglyMeasurable.mul (memLp_fam_comp F p.2 0).1)
    · exact (aestronglyMeasurable_termSum F t L fun q hq => (hL' q hq).1.continuous_right t).sub
        (aestronglyMeasurable_termSum F 0 L fun q hq => (hL' q hq).1.continuous_right 0)

/-- `‖F‖ ≤ ∑_{|α| ≤ j} ‖∂^α f‖`. -/
theorem norm_le_sum_der (X : HjM j M) : ‖X‖ ≤ ∑ α : Idx j, ‖X.der α‖ := by
  have hs := HjM.norm_sq X
  have hsum : 0 ≤ ∑ α : Idx j, ‖X.der α‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h2 : ∑ α : Idx j, ‖X.der α‖ ^ 2 ≤ (∑ α : Idx j, ‖X.der α‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _
  rw [← hs] at h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hsum two_ne_zero).1 h2

/-- **Strong continuity at `t = 0`**: `T(t)f → f` in `H^j_M` as `t → 0`. -/
theorem tendsto_transport_zero (F : HjM j M) :
    Tendsto (fun t => transport j M t F) (𝓝 0) (𝓝 F) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hder : ∀ α : Idx j,
      Tendsto (fun t => ‖(transport j M t F).der α - F.der α‖) (𝓝 0) (𝓝 0) := by
    intro α
    have h0 : transportFun 0 F = F := by
      rw [← transport_apply, transport_zero]
      rfl
    have hF := der_transportFun_ae 0 F α
    rw [h0] at hF
    have h := tendsto_termSum F (terms (pdList α.1)) (terms_good _)
    have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at h'
    refine h'.congr' (Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply]
    rw [Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub ((transport j M t F).der α) (F.der α),
      der_transportFun_ae t F α, hF] with y e1 e2 e3
    rw [e1, Pi.sub_apply, Pi.sub_apply, transport_apply, e2, e3]
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Idx j)) fun α _ => hder α
  rw [Finset.sum_const_zero] at hsum
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => (norm_le_sum_der _).trans_eq ?_) hsum
  rfl

/-- **Strong continuity** (`paper/main.tex:1238`): `t ↦ T(t)f` is continuous `ℝ → H^j_M` for
every `f ∈ H^j_M`. -/
theorem continuous_transport_apply (F : HjM j M) : Continuous fun t => transport j M t F := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hs : Tendsto (fun t : ℝ => t - t₀) (𝓝 t₀) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 t₀)).sub_const t₀
  have h := ((transport j M t₀).continuous.tendsto F).comp ((tendsto_transport_zero F).comp hs)
  refine h.congr fun t => ?_
  simp only [Function.comp_apply]
  rw [← ContinuousLinearMap.comp_apply, ← transport_add, add_sub_cancel]

end UnforcedLeray.B0063
