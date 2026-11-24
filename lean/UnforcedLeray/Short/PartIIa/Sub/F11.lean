import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Units.B0449.GraphResolventUniformBound

/-!
# Part II-a, task `PartII-a:F11`: the supremum embedding (conditional on one explicit bound)

Source of record: `the November 2 reference manuscript`, lines 1524-1531
(`bg:supremum-embedding`: unit strip pullback `W(t,z) = w(τ₀+t, e^{-t/2}(y₀+√ν z))`, fixed time
cutoff `χ`, source `F = (∂_t - Δ_z + 1)(χ W)`, causal kernel `k ∈ L^{r'}` iff `r > 5/2`,
`χ W = k * F`, Hölder at `(0,0)`).

The library (Units/B0449/GraphResolvent*.lean) already contains the whole chart machinery:
a globally continuous scalar chart representative `globalChartRep` of `dotL e (w(τ,·))`
(`continuous_globalChartRep`), its identification with the phase trace at every phase
(`globalChartRep_ae_phaseScalar`), and a pointwise bound
`‖globalChartRep … τ y‖ ≤ ‖k‖_{L^{r'}} ‖F‖_{L^r}` (`chartJ_cutoff_ST_continuous_rep`,
`exists_globalChartRep_uniform_bound`). What is missing is the explicit dependence of the
source norm `‖F‖_{L^r}` on `ν`, `‖w‖`, `‖νΔw‖`, `‖𝒯w‖`: the existing theorem
`chartJ_cutoff_FST_uniform_eLpNorm` only produces an unspecified finite `C`. Its proof
(Units/B0449/GraphResolventBounded.lean lines 107-282) in fact constructs
`C = ofReal Mχt * Cw + ofReal Mχ * Cb + ofReal (Mχ e^{1/2}) * Ca + ofReal Mχ * Cw` with
`Cw = ‖dotL e‖ * (2 e^{3/4} ν^{-3/2})^{1/q} * ‖w‖` (and `Ca`, `Cb` likewise), which is exactly
the quantitative statement `ChartCutoffExplicit` below (the one new lemma; proved as
`chartCutoffExplicit` in `Short/PartII-a/Tasks/F11SupEmbedding.lean`, which also states the
unconditional theorem).

This file proves, from `ChartCutoffExplicit` alone:

* `exists_globalChartRep_bound_explicit`: the pointwise bound
  `‖globalChartRep … e τ y‖ ≤ K ‖dotL e‖ ν^{-3/(2q)} (‖w‖ + ‖𝒯w‖ + ‖νΔw‖)`, `K` independent of
  `P, ν, w, e, τ, y`;
* `globalChartRep_periodic`: `τ`-periodicity of the chart representative (from the every-phase
  identification and uniqueness of continuous representatives);
* `graphSupEmbedding_of`: assembly of the three coordinate representatives into the continuous
  `W : AddCircle P × ℝ³ → ℂ³` of `GraphSupEmbedding`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.PhaseTrace
  UnforcedLeray.B0449 UnforcedLeray.Heat

/-- **Explicit cutoff-source bound** (source lines 1524-1531, "the right side
`F = (∂_t - Δ_z + 1)(χ W)` has this same bound"). For every `q = qR > 5/2` there is `K ≥ 0` such
that, for all `0 < P ≤ 1`, `ν > 0`, `w, a = νΔw, b = 𝒯w ∈ Y_q`, every observation direction `e`
and every chart time `τ₀`, the `L^q(ℝ × ℝ³)` norm of the cutoff chart source
`chartJCutoffFST ν τ₀ e w b a` is at most `K ‖dotL e‖ ν^{-3/(2q)} (‖w‖ + ‖b‖ + ‖a‖)`.
(The existing `chartJ_cutoff_FST_uniform_eLpNorm` is the same statement with an unspecified
finite bound in place of the displayed one.) -/
def ChartCutoffExplicit : Prop :=
  ∀ (qR : ℝ), 5 / 2 < qR → ∀ [Fact (1 ≤ ENNReal.ofReal qR)], ∃ K : ℝ, 0 ≤ K ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν →
      ∀ (w a b : Yq P (ENNReal.ofReal qR)) (e : CVec3) (τ₀ : ℝ),
        eLpNorm (chartJCutoffFST ν τ₀ e w b a) (ENNReal.ofReal qR) volume ≤
          ENNReal.ofReal (K * ‖dotL e‖ * ν ^ (-(3 / (2 * qR))) * (‖w‖ + ‖b‖ + ‖a‖))

/-! ### The pointwise bound with explicit dependence -/

/-- Pointwise bound of the chart representative with explicit `ν`-, `w`- and `e`-dependence. -/
theorem exists_globalChartRep_bound_explicit (hN : ChartCutoffExplicit) {qR qR' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal qR)] (hqq' : qR.HolderConjugate qR') (hq : 5 / 2 < qR) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℝ) [Fact (0 < P)] (hP1 : P ≤ 1) (ν : ℝ) (hν : 0 < ν)
      (w a b : Yq P (ENNReal.ofReal qR)) (hTime : HasPhaseOp driftT w b)
      (hLap : HasPhaseOp (nuLapT ν) w a) (e : CVec3) (τ : ℝ) (y : Space),
      ‖globalChartRep hP1 hqq' hq hν hTime hLap e τ y‖ ≤
        K * ‖dotL e‖ * ν ^ (-(3 / (2 * qR))) * (‖w‖ + ‖b‖ + ‖a‖) := by
  obtain ⟨K1, hK1, hK1b⟩ := hN qR hq
  let Kst : ℝ := (eLpNorm stKernel (ENNReal.ofReal qR') volume).toReal
  have hKst : 0 ≤ Kst := ENNReal.toReal_nonneg
  refine ⟨Kst * K1, mul_nonneg hKst hK1, ?_⟩
  intro P _ hP1 ν hν w a b hTime hLap e τ y
  obtain ⟨H, F, hHae, hFae, hHF, ⟨Hc, hHc, hHraw, hHbound⟩, hUniformτ⟩ :=
    chartJ_cutoff_ST_continuous_rep hP1 hqq' hq hν hTime hLap τ e
  let Bd : ℝ := K1 * ‖dotL e‖ * ν ^ (-(3 / (2 * qR))) * (‖w‖ + ‖b‖ + ‖a‖)
  have hBd : 0 ≤ Bd := by
    have : 0 ≤ ν ^ (-(3 / (2 * qR))) := Real.rpow_nonneg hν.le _
    dsimp [Bd]
    positivity
  let f : ℝ × Space → ℂ := chosenLocalChart hP1 hqq' hq hν hTime hLap e τ
  let B : ℝ × Space → ℂ := fun p => Hc (productToST p)
  have hBcont : Continuous B := hHc.comp productToST.continuous
  have hpull : B =ᵐ[volume] fun p => chartJCutoffHST ν τ e w (productToST p) :=
    (B0448.measurePreserving_ofLp.symm).quasiMeasurePreserving.ae_eq_comp hHraw.symm
  have hS : MeasurableSet chartCentral := measurableSet_Ioo.prod MeasurableSet.univ
  have hBcentral : B =ᵐ[volume.restrict chartCentral]
      (fun p => dotL e (chartJ w ν τ p)) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hS]
    filter_upwards [hpull] with p hp hpS
    have ht : |p.1| ≤ 1 / 8 := by
      rw [abs_le]
      constructor <;> linarith [hpS.1.1, hpS.1.2]
    have hχ := resolventTimeCutoff_eq_one ht
    simpa [B, chartJCutoffHST, productToST, hχ] using hp
  have hchosen := chosenLocalChart_ae hP1 hqq' hq hν hTime hLap e τ
  have hEqOn := Measure.eqOn_open_of_ae_eq (hchosen.trans hBcentral.symm)
    isOpen_chartCentral (continuous_chosenLocalChart hP1 hqq' hq hν hTime hLap e τ).continuousOn
    hBcont.continuousOn
  have hp : (0, (Real.sqrt ν)⁻¹ • y) ∈ chartCentral := by
    simp [chartCentral]
  have hpoint := hEqOn hp
  have hsourceBound :
      ‖Hc (productToST (0, (Real.sqrt ν)⁻¹ • y))‖ ≤ Kst * Bd := by
    have hreal : (eLpNorm (chartJCutoffFST ν τ e w b a)
        (ENNReal.ofReal qR) volume).toReal ≤ Bd :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hK1b P hP1 ν hν w a b e τ)).trans
        (ENNReal.toReal_ofReal hBd).le
    calc
      _ ≤ (eLpNorm stKernel (ENNReal.ofReal qR') volume).toReal *
          (eLpNorm (chartJCutoffFST ν τ e w b a) (ENNReal.ofReal qR) volume).toReal :=
        hHbound (productToST (0, (Real.sqrt ν)⁻¹ • y))
      _ ≤ Kst * Bd := mul_le_mul_of_nonneg_left hreal hKst
  have hcomplex :
      ‖globalChartRep hP1 hqq' hq hν hTime hLap e τ y‖ ≤ Kst * Bd := by
    change ‖f (0, (Real.sqrt ν)⁻¹ • y)‖ ≤ Kst * Bd
    change ‖chosenLocalChart hP1 hqq' hq hν hTime hLap e τ
      (0, (Real.sqrt ν)⁻¹ • y)‖ ≤ Kst * Bd
    rw [hpoint]
    change ‖Hc (productToST (0, (Real.sqrt ν)⁻¹ • y))‖ ≤ Kst * Bd
    exact hsourceBound
  calc ‖globalChartRep hP1 hqq' hq hν hTime hLap e τ y‖ ≤ Kst * Bd := hcomplex
    _ = Kst * K1 * ‖dotL e‖ * ν ^ (-(3 / (2 * qR))) * (‖w‖ + ‖b‖ + ‖a‖) := by
      dsimp [Bd]; ring

/-! ### Periodicity of the chart representative -/

section Periodic

variable {P qR qR' ν : ℝ}
variable [Fact (0 < P)] [Fact (1 ≤ ENNReal.ofReal qR)]
variable (hP1 : P ≤ 1) (hqq' : qR.HolderConjugate qR') (hq : 5 / 2 < qR)
variable (hν : 0 < ν)
variable {w a b : Yq P (ENNReal.ofReal qR)}
variable (hTime : HasPhaseOp driftT w b) (hLap : HasPhaseOp (nuLapT ν) w a)
variable (e : CVec3)

/-- The glued scalar representative is `P`-periodic in the phase: both `y ↦ rep(τ + P, y)` and
`y ↦ rep(τ, y)` are continuous and agree a.e. with the same phase trace. -/
theorem globalChartRep_periodic (τ : ℝ) (y : Space) :
    globalChartRep hP1 hqq' hq hν hTime hLap e (τ + P) y =
      globalChartRep hP1 hqq' hq hν hTime hLap e τ y := by
  have h1 := globalChartRep_ae_phaseScalar hP1 hqq' hq hν hTime hLap e (τ + P)
  have h2 := globalChartRep_ae_phaseScalar hP1 hqq' hq hν hTime hLap e τ
  have hs : phaseScalarPath hTime e (τ + P) = phaseScalarPath hTime e τ := by
    unfold phaseScalarPath
    rw [AddCircle.coe_add_period]
  rw [hs] at h1
  have hcont := continuous_globalChartRep hP1 hqq' hq hν hTime hLap e
  have hc : ∀ s : ℝ, Continuous (fun y : Space =>
      globalChartRep hP1 hqq' hq hν hTime hLap e s y) := by
    intro s
    exact Continuous.comp
      (g := fun p : ℝ × Space => globalChartRep hP1 hqq' hq hν hTime hLap e p.1 p.2)
      (f := fun y : Space => ((s, y) : ℝ × Space)) hcont (continuous_const.prodMk continuous_id)
  have heq := Continuous.ae_eq_iff_eq (volume : Measure Space) (hc (τ + P)) (hc τ) |>.1
    (h1.trans h2.symm)
  exact congrFun heq y

/-- The vector of the three coordinate chart representatives, as a function on `ℝ × ℝ³`. -/
def chartVec (hP1 : P ≤ 1) (hqq' : qR.HolderConjugate qR') (hq : 5 / 2 < qR) (hν : 0 < ν)
    (hTime : HasPhaseOp driftT w b) (hLap : HasPhaseOp (nuLapT ν) w a) (τ : ℝ) (y : Space) :
    CVec3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    globalChartRep hP1 hqq' hq hν hTime hLap (complexCoordinate i) τ y)

theorem continuous_chartVec : Continuous
    (fun p : ℝ × Space => chartVec hP1 hqq' hq hν hTime hLap p.1 p.2) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp
    (continuous_pi fun i => continuous_globalChartRep hP1 hqq' hq hν hTime hLap
      (complexCoordinate i))

theorem chartVec_periodic (τ : ℝ) (y : Space) :
    chartVec hP1 hqq' hq hν hTime hLap (τ + P) y = chartVec hP1 hqq' hq hν hTime hLap τ y := by
  unfold chartVec
  congr 1
  funext i
  exact globalChartRep_periodic hP1 hqq' hq hν hTime hLap (complexCoordinate i) τ y

theorem chartVec_ae_phaseRepC (τ : ℝ) :
    (fun y => chartVec hP1 hqq' hq hν hTime hLap τ y) =ᵐ[volume]
      (fun y => phaseRepC (q := ENNReal.ofReal qR) (by exact ENNReal.ofReal_ne_top)
        hTime (τ : AddCircle P) y) := by
  have hcoord : ∀ i : Fin 3,
      (fun y => globalChartRep hP1 hqq' hq hν hTime hLap (complexCoordinate i) τ y) =ᵐ[volume]
        (fun y => phaseRepC (q := ENNReal.ofReal qR) (by exact ENNReal.ofReal_ne_top)
          hTime (τ : AddCircle P) y i) := by
    intro i
    have hglobal := globalChartRep_ae_phaseScalar hP1 hqq' hq hν hTime hLap
      (complexCoordinate i) τ
    have hcoerce := coeFn_phaseScalarPath hTime (complexCoordinate i) τ
    filter_upwards [hglobal, hcoerce] with y hy hy'
    rw [dotL_complexCoordinate] at hy'
    exact hy.trans hy'
  rw [Filter.EventuallyEq]
  filter_upwards [ae_all_iff.2 hcoord] with y hy
  ext i
  exact hy i

end Periodic

/-- Euclidean norm of a complex 3-vector is at most the sum of its coordinate norms. -/
theorem supEmb_norm_cvec3_le (v : CVec3) : ‖v‖ ≤ ‖v 0‖ + ‖v 1‖ + ‖v 2‖ := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp only [Fin.sum_univ_three]
  nlinarith [norm_nonneg (v 0), norm_nonneg (v 1), norm_nonneg (v 2)]

/-- The coordinate functional `dotL (complexCoordinate i)` has norm at most `1`. -/
theorem supEmb_norm_dotL_cc_le (i : Fin 3) : ‖dotL (complexCoordinate i)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [dotL_complexCoordinate, one_mul]
  exact PiLp.norm_apply_le v i

/-- **`PartII-a:F11`, conditional on the explicit cutoff-source bound.** The supremum embedding
`bg:supremum-embedding` (source lines 1524-1531) follows from `ChartCutoffExplicit`: the three
coordinate chart representatives are continuous (`continuous_globalChartRep`), `P`-periodic
(`globalChartRep_periodic`), agree with the phase trace at every phase
(`globalChartRep_ae_phaseScalar`), descend to `AddCircle P × ℝ³` through the open quotient map
`mk × id`, and satisfy the explicit pointwise bound. The constant is `3 K` with `K` from the
Hölder step with the causal kernel, independent of `P ≤ 1`, `ν`, `w`. -/
theorem graphSupEmbedding_of (hN : ChartCutoffExplicit) : GraphSupEmbedding := by
  intro r _ hr5 hrtop
  obtain ⟨qR, hqR0, rfl⟩ : ∃ qR : ℝ, 0 ≤ qR ∧ r = ENNReal.ofReal qR :=
    ⟨r.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hrtop).symm⟩
  have hq : 5 / 2 < qR := by
    have h52 : (5 / 2 : ℝ≥0∞) = ENNReal.ofReal (5 / 2) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    rw [h52] at hr5
    have hqpos : 0 < qR := by
      by_contra h
      rw [not_lt] at h
      rw [ENNReal.ofReal_of_nonpos h] at hr5
      simp at hr5
    exact (ENNReal.ofReal_lt_ofReal_iff hqpos).1 hr5
  have hqq' : qR.HolderConjugate (Real.conjExponent qR) :=
    Real.HolderConjugate.conjExponent (by linarith)
  obtain ⟨K, hK0, hKb⟩ := exists_globalChartRep_bound_explicit hN hqq' hq
  refine ⟨3 * K, by positivity, ?_⟩
  intro P _ hP1 ν hν w
  have hTime := hasPhaseOp_T0D w
  have hLap := hasPhaseOp_nuLapD w
  have hper : ∀ y : Space,
      Function.Periodic (fun t : ℝ => chartVec hP1 hqq' hq hν hTime hLap t y) P :=
    fun y t => chartVec_periodic hP1 hqq' hq hν hTime hLap t y
  let W : AddCircle P × Space → CVec3 := fun z => (hper z.2).lift z.1
  have hWcoe : ∀ (t : ℝ) (y : Space),
      W ((t : AddCircle P), y) = chartVec hP1 hqq' hq hν hTime hLap t y := fun t y => rfl
  have hWcont : Continuous W := by
    have hq' : IsOpenQuotientMap
        (Prod.map (QuotientAddGroup.mk : ℝ → AddCircle P) (id : Space → Space)) :=
      QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id
    rw [← hq'.continuous_comp_iff]
    exact continuous_chartVec hP1 hqq' hq hν hTime hLap
  refine ⟨W, hWcont, ?_, ?_⟩
  · have h1 := phaseRepC_ae (q := ENNReal.ofReal qR) hrtop hTime
    filter_upwards [h1] with τ hτ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective τ
    have h2 := chartVec_ae_phaseRepC hP1 hqq' hq hν hTime hLap t
    have h3 : ⇑((w : Yq P (ENNReal.ofReal qR)) (t : AddCircle P)) =
        ⇑(phaseRepC (q := ENNReal.ofReal qR) hrtop hTime (t : AddCircle P)) := by
      rw [hτ]
    rw [h3]
    exact h2
  · intro τ y
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective τ
    rw [hWcoe, ENNReal.toReal_ofReal hqR0]
    have hnorm := supEmb_norm_cvec3_le (chartVec hP1 hqq' hq hν hTime hLap t y)
    have hb : ∀ i : Fin 3, ‖chartVec hP1 hqq' hq hν hTime hLap t y i‖ ≤
        K * ν ^ (-(3 / (2 * qR))) * graphNormD w := by
      intro i
      have h := hKb P hP1 ν hν (w : Yq P (ENNReal.ofReal qR)) (nuLapD w) (T0D w) hTime hLap
        (complexCoordinate i) t y
      have hν' : 0 ≤ ν ^ (-(3 / (2 * qR))) := Real.rpow_nonneg hν.le _
      have hS : 0 ≤ ‖(w : Yq P (ENNReal.ofReal qR))‖ + ‖T0D w‖ + ‖nuLapD w‖ := by positivity
      have hd := supEmb_norm_dotL_cc_le i
      have hg : graphNormD w = ‖(w : Yq P (ENNReal.ofReal qR))‖ + ‖T0D w‖ + ‖nuLapD w‖ := by
        unfold graphNormD; ring
      rw [hg]
      refine h.trans ?_
      have : K * ‖dotL (complexCoordinate i)‖ ≤ K * 1 := mul_le_mul_of_nonneg_left hd hK0
      calc K * ‖dotL (complexCoordinate i)‖ * ν ^ (-(3 / (2 * qR))) *
            (‖(w : Yq P (ENNReal.ofReal qR))‖ + ‖T0D w‖ + ‖nuLapD w‖)
          ≤ K * 1 * ν ^ (-(3 / (2 * qR))) *
            (‖(w : Yq P (ENNReal.ofReal qR))‖ + ‖T0D w‖ + ‖nuLapD w‖) := by gcongr
        _ = K * ν ^ (-(3 / (2 * qR))) *
            (‖(w : Yq P (ENNReal.ofReal qR))‖ + ‖T0D w‖ + ‖nuLapD w‖) := by ring
    have h0 := hb 0
    have h1 := hb 1
    have h2 := hb 2
    nlinarith

end UnforcedLeray.Short.PartIIa
