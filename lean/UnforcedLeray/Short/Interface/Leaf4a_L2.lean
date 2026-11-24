import UnforcedLeray.Short.Interface.WindowSteps
import UnforcedLeray.Units.B0424.Chart

/-!
# Interface: `L²` bounds of the window chart pieces (step W2, `windowChartL2`)

Proves `windowChartL2 : WindowChartL2` (`WindowSteps.lean`): for a `𝒴₂` field `w`, a `𝒴₂` field
`f` and a window cutoff `χ`, the chart functions `windowU` and `windowF` are in `L²(ℝ × ℝ³)`.

Source of record: `the November 2 reference manuscript`; the window argument of the
old manuscript, `paper/main.tex` lines 7479-7536 (`q = 2`), with the Jacobians `dx = e^{3t/2} dy`
and `dθ = e^t dt` of `Units/B0424/Chart.lean`.

Strategy. Each piece is `indicator(θ > 0) (a(log θ) · v(log θ, x))` with a bounded weight `a`
supported in `(-2, 2)`. The lower integral is pulled back along `expChart` (`lintegral_expChart'`)
and `dilChart` (`lintegral_dilChart'`); the integrand becomes `e^{3t/2} a(t)² ‖w(τ₀+t, y)‖²`.
The window integral `∫_{(-2,2)} ∫_y ‖w(τ₀+t, y)‖² dy dt` is finite by periodicity: a bounded
interval is covered by finitely many period slabs (`lintegral_Ioo_lt_top_of_periodic`).
Measurability comes from the quasi-measure-preserving chart map `chartPsi`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.B0424

/-! ## 1. Generic helpers -/

theorem memLp_two_of_lintegral_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {F : α → E} (hF : AEStronglyMeasurable F μ)
    (h : ∫⁻ a, ‖F a‖ₑ ^ 2 ∂μ < ⊤) : MemLp F 2 μ := by
  refine ⟨hF, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).2 ?_⟩
  simpa [ENNReal.rpow_two] using h

theorem lintegral_sq_lt_top_of_memLp {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {F : α → E} (hF : MemLp F 2 μ) : ∫⁻ a, ‖F a‖ₑ ^ 2 ∂μ < ⊤ := by
  have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).1
    hF.eLpNorm_lt_top
  simpa [ENNReal.rpow_two] using h

theorem enorm_sq_real (r : ℝ) : ‖r‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg r), sq_abs]

theorem enorm_sq_eq_ofReal_norm {E : Type*} [NormedAddCommGroup E] (v : E) :
    ‖v‖ₑ ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  have h : ‖v‖ₑ = ENNReal.ofReal ‖v‖ := by
    first
    | exact (ofReal_norm v).symm
    | exact (ENNReal.ofReal_norm v).symm
    | exact (ofReal_norm_eq_enorm v).symm
    | exact (ENNReal.ofReal_norm_eq_enorm v).symm
    | simp [ENNReal.ofReal, enorm_eq_nnnorm]
  rw [h, ENNReal.ofReal_pow (norm_nonneg v)]

theorem lintegral_Ioc_shift_period {P : ℝ} (hP : 0 < P) {G : ℝ → ℝ≥0∞}
    (hper : Function.Periodic G P) (s : ℝ) :
    ∫⁻ σ in Ioc s (s + P), G σ = ∫⁻ σ in Ioc 0 P, G σ := by
  have : VAddInvariantMeasure (AddSubgroup.zmultiples P) ℝ volume :=
    ⟨fun c t _ => measure_preimage_add _ _ _⟩
  have h2 := (isAddFundamentalDomain_Ioc hP s).setLIntegral_eq
    (isAddFundamentalDomain_Ioc hP 0) G hper.map_vadd_zmultiples
  rwa [zero_add] at h2

theorem lintegral_Ioc_nat_period_real {P : ℝ} (hP : 0 < P) {G : ℝ → ℝ≥0∞}
    (hper : Function.Periodic G P) (b : ℝ) (n : ℕ) :
    ∫⁻ σ in Ioc b (b + n * P), G σ = n * ∫⁻ σ in Ioc 0 P, G σ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : Ioc b (b + ((n + 1 : ℕ) : ℝ) * P) =
        Ioc b (b + n * P) ∪ Ioc (b + n * P) (b + n * P + P) := by
      rw [Ioc_union_Ioc_eq_Ioc]
      · congr 1
        push_cast
        ring
      · have : 0 ≤ (n : ℝ) * P := mul_nonneg (Nat.cast_nonneg n) hP.le
        linarith
      · linarith
    rw [hsplit, lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl), ih,
      lintegral_Ioc_shift_period hP hper]
    push_cast
    ring

theorem lintegral_Ioo_lt_top_of_periodic {P : ℝ} (hP : 0 < P) {G : ℝ → ℝ≥0∞}
    (hper : Function.Periodic G P) (hfin : ∫⁻ σ in Ioc 0 P, G σ < ⊤) (a b : ℝ) :
    ∫⁻ σ in Ioo a b, G σ < ⊤ := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b - a ≤ n * P :=
    ⟨⌈(b - a) / P⌉₊, by
      have h1 : (b - a) / P ≤ (⌈(b - a) / P⌉₊ : ℝ) := Nat.le_ceil _
      rwa [div_le_iff₀ hP] at h1⟩
  have hsub : Ioo a b ⊆ Ioc a (a + n * P) := fun t ht => ⟨ht.1, by linarith [ht.2]⟩
  refine (lintegral_mono_set hsub).trans_lt ?_
  rw [lintegral_Ioc_nat_period_real hP hper a n]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top n) hfin

/-- Tonelli for a weight depending only on the phase: the phase `S`-indicator. -/
theorem tonelli_indicator {F : ℝ × Space → ℝ≥0∞} (hF : AEMeasurable F volume)
    {S : Set ℝ} (hS : MeasurableSet S) :
    ∫⁻ p, S.indicator (1 : ℝ → ℝ≥0∞) p.1 * F p =
      ∫⁻ τ, S.indicator (1 : ℝ → ℝ≥0∞) τ * ∫⁻ y, F (τ, y) := by
  have hprod : ∫⁻ p, S.indicator (1 : ℝ → ℝ≥0∞) p.1 * F p =
      ∫⁻ p in S ×ˢ (univ : Set Space), F p := by
    rw [← lintegral_indicator (hS.prod MeasurableSet.univ)]
    refine lintegral_congr fun p => ?_
    by_cases h : p.1 ∈ S
    · have hp : p ∈ S ×ˢ (univ : Set Space) := ⟨h, trivial⟩
      simp only [Set.indicator_of_mem h, Set.indicator_of_mem hp, Pi.one_apply, one_mul]
    · have hp : p ∉ S ×ˢ (univ : Set Space) := fun hp' => h hp'.1
      simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem hp, zero_mul]
  rw [hprod, Measure.volume_eq_prod,
    setLIntegral_prod F (hF.mono_measure Measure.restrict_le_self)]
  simp only [Measure.restrict_univ]
  rw [← lintegral_indicator hS]
  refine lintegral_congr fun τ => ?_
  by_cases h : τ ∈ S
  · simp only [Set.indicator_of_mem h, Pi.one_apply, one_mul]
  · simp only [Set.indicator_of_notMem h, zero_mul]

/-! ## 2. Finiteness of the window integral -/

theorem window_lintegral_lt_top {P : ℝ} (hP : 0 < P) {g : ℝ → SpatialField}
    (hg : B0005.IsY2 P g) (τ₀ : ℝ) :
    ∫⁻ p : ℝ × Space, (Ioo (-2:ℝ) 2).indicator (1 : ℝ → ℝ≥0∞) p.1 * ‖g (τ₀ + p.1) p.2‖ₑ ^ 2
      < ⊤ := by
  have hF : AEMeasurable (fun z : ℝ × Space => ‖g z.1 z.2‖ₑ ^ 2) volume :=
    (hg.measurable.enorm).pow_const 2
  have hpt : ∀ p : ℝ × Space,
      (Ioo (-2:ℝ) 2).indicator (1 : ℝ → ℝ≥0∞) p.1 * ‖g (τ₀ + p.1) p.2‖ₑ ^ 2 =
        (Ioo (τ₀ - 2) (τ₀ + 2)).indicator (1 : ℝ → ℝ≥0∞) (τ₀ + p.1) *
          ‖g (τ₀ + p.1) p.2‖ₑ ^ 2 := by
    intro p
    have hm : p.1 ∈ Ioo (-2:ℝ) 2 ↔ τ₀ + p.1 ∈ Ioo (τ₀ - 2) (τ₀ + 2) := by
      simp only [Set.mem_Ioo]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    by_cases h : p.1 ∈ Ioo (-2:ℝ) 2
    · simp only [Set.indicator_of_mem h, Set.indicator_of_mem (hm.1 h), Pi.one_apply]
    · simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hm.2 h), zero_mul]
  have hfin : ∫⁻ σ in Ioc 0 P, ∫⁻ y : Space, ‖g σ y‖ₑ ^ 2 < ⊤ := by
    have hL : ∫⁻ z in Ioc 0 P ×ˢ (univ : Set Space), ‖g z.1 z.2‖ₑ ^ 2 < ⊤ :=
      lintegral_sq_lt_top_of_memLp hg.memL2
    have e1 : ∫⁻ z in Ioc 0 P ×ˢ (univ : Set Space), ‖g z.1 z.2‖ₑ ^ 2 =
        ∫⁻ z : ℝ × Space, (Ioc 0 P).indicator (1 : ℝ → ℝ≥0∞) z.1 * ‖g z.1 z.2‖ₑ ^ 2 := by
      rw [← lintegral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]
      refine lintegral_congr fun z => ?_
      by_cases h : z.1 ∈ Ioc 0 P
      · have hz : z ∈ Ioc 0 P ×ˢ (univ : Set Space) := ⟨h, trivial⟩
        simp only [Set.indicator_of_mem hz, Set.indicator_of_mem h, Pi.one_apply, one_mul]
      · have hz : z ∉ Ioc 0 P ×ˢ (univ : Set Space) := fun hz' => h hz'.1
        simp only [Set.indicator_of_notMem hz, Set.indicator_of_notMem h, zero_mul]
    have e2 : ∫⁻ z : ℝ × Space, (Ioc 0 P).indicator (1 : ℝ → ℝ≥0∞) z.1 * ‖g z.1 z.2‖ₑ ^ 2 =
        ∫⁻ σ, (Ioc 0 P).indicator (1 : ℝ → ℝ≥0∞) σ * ∫⁻ y : Space, ‖g σ y‖ₑ ^ 2 :=
      tonelli_indicator hF measurableSet_Ioc
    have e3 : ∫⁻ σ, (Ioc 0 P).indicator (1 : ℝ → ℝ≥0∞) σ * ∫⁻ y : Space, ‖g σ y‖ₑ ^ 2 =
        ∫⁻ σ in Ioc 0 P, ∫⁻ y : Space, ‖g σ y‖ₑ ^ 2 := by
      rw [← lintegral_indicator measurableSet_Ioc]
      refine lintegral_congr fun σ => ?_
      by_cases h : σ ∈ Ioc 0 P
      · simp only [Set.indicator_of_mem h, Pi.one_apply, one_mul]
      · simp only [Set.indicator_of_notMem h, zero_mul]
    have hslab := e1.trans (e2.trans e3)
    rw [← hslab]
    exact hL
  have hper : Function.Periodic (fun τ : ℝ => ∫⁻ y : Space, ‖g τ y‖ₑ ^ 2) P := fun τ => by
    show ∫⁻ y : Space, ‖g (τ + P) y‖ₑ ^ 2 = ∫⁻ y : Space, ‖g τ y‖ₑ ^ 2
    rw [hg.periodic τ]
  have hshift : ∫⁻ p : ℝ × Space,
      (Ioo (τ₀ - 2) (τ₀ + 2)).indicator (1 : ℝ → ℝ≥0∞) (τ₀ + p.1) *
        ‖g (τ₀ + p.1) p.2‖ₑ ^ 2 =
      ∫⁻ p : ℝ × Space, (Ioo (τ₀ - 2) (τ₀ + 2)).indicator (1 : ℝ → ℝ≥0∞) p.1 *
        ‖g p.1 p.2‖ₑ ^ 2 :=
    lintegral_shift τ₀ (fun z : ℝ × Space =>
      (Ioo (τ₀ - 2) (τ₀ + 2)).indicator (1 : ℝ → ℝ≥0∞) z.1 * ‖g z.1 z.2‖ₑ ^ 2)
  have hT : ∫⁻ p : ℝ × Space, (Ioo (τ₀ - 2) (τ₀ + 2)).indicator (1 : ℝ → ℝ≥0∞) p.1 *
        ‖g p.1 p.2‖ₑ ^ 2 =
      ∫⁻ τ, (Ioo (τ₀ - 2) (τ₀ + 2)).indicator (1 : ℝ → ℝ≥0∞) τ *
        ∫⁻ y : Space, ‖g τ y‖ₑ ^ 2 :=
    tonelli_indicator hF measurableSet_Ioo
  have h4 : ∀ τ : ℝ, (Ioo (τ₀ - 2) (τ₀ + 2)).indicator (1 : ℝ → ℝ≥0∞) τ *
      (∫⁻ y : Space, ‖g τ y‖ₑ ^ 2) =
      (Ioo (τ₀ - 2) (τ₀ + 2)).indicator (fun τ : ℝ => ∫⁻ y : Space, ‖g τ y‖ₑ ^ 2) τ := by
    intro τ
    by_cases h : τ ∈ Ioo (τ₀ - 2) (τ₀ + 2)
    · simp only [Set.indicator_of_mem h, Pi.one_apply, one_mul]
    · simp only [Set.indicator_of_notMem h, zero_mul]
  have hmain : ∫⁻ p : ℝ × Space,
      (Ioo (-2:ℝ) 2).indicator (1 : ℝ → ℝ≥0∞) p.1 * ‖g (τ₀ + p.1) p.2‖ₑ ^ 2 =
      ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2), ∫⁻ y : Space, ‖g τ y‖ₑ ^ 2 := by
    rw [lintegral_congr hpt, hshift, hT, lintegral_congr h4, lintegral_indicator measurableSet_Ioo]
  rw [hmain]
  exact lintegral_Ioo_lt_top_of_periodic hP hper hfin (τ₀ - 2) (τ₀ + 2)

/-! ## 3. The chart maps -/

/-- The composite chart `(θ, x) ↦ (τ₀ + log θ, e^{-(log θ)/2} x)`: the phase shift of the
dilation inverse of the time chart (`expChart`, `dilChartInv`). -/
def chartPsi (τ₀ : ℝ) (X : ℝ × Space) : ℝ × Space :=
  (τ₀ + Real.log X.1, Real.exp (-(Real.log X.1 / 2)) • X.2)

theorem chart_dilChart (τ₀ : ℝ) (g : ℝ → SpatialField) (i : Fin 3) (p : ℝ × Space) :
    chartField τ₀ g p.1 (Real.exp (p.1 / 2) • p.2) i =
      Real.exp (-(p.1 / 2)) * g (τ₀ + p.1) p.2 i := by
  simp only [chartField, PiLp.smul_apply, smul_eq_mul, smul_smul, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, one_smul]

theorem qmp_chartPsi (τ₀ : ℝ) :
    Measure.QuasiMeasurePreserving (chartPsi τ₀)
      (volume.restrict (Ioi (0:ℝ) ×ˢ (univ : Set Space))) volume := by
  have hlog : Measurable fun X : ℝ × Space => Real.log X.1 :=
    Real.measurable_log.comp measurable_fst
  have hexp : Measurable fun X : ℝ × Space => Real.exp (-(Real.log X.1 / 2)) :=
    Real.measurable_exp.comp (hlog.div_const 2).neg
  have hmeas : Measurable (chartPsi τ₀) :=
    (measurable_const.add hlog).prodMk (hexp.smul measurable_snd)
  refine ⟨hmeas, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  have hT : Measurable fun p : ℝ × Space => (τ₀ + p.1, p.2) :=
    (measurable_const.add measurable_fst).prodMk measurable_snd
  have hTs : MeasurableSet ((fun p : ℝ × Space => (τ₀ + p.1, p.2)) ⁻¹' s) := hT hs
  have hT0 : volume ((fun p : ℝ × Space => (τ₀ + p.1, p.2)) ⁻¹' s) = 0 := by
    rw [show (fun p : ℝ × Space => (τ₀ + p.1, p.2)) =
        fun p => ((τ₀, 0) : ℝ × Space) + p from (shift_eq τ₀).symm, measure_preimage_add]
    exact hs0
  have key : ∀ p : ℝ × Space,
      rhoE p * (chartPsi τ₀ ⁻¹' s).indicator (1 : ℝ × Space → ℝ≥0∞) (expChart p) =
        (fun q : ℝ × Space => rhoE q * s.indicator (1 : ℝ × Space → ℝ≥0∞) (τ₀ + q.1, q.2))
          (dilChartInv p) := by
    intro p
    show rhoE p * (chartPsi τ₀ ⁻¹' s).indicator (1 : ℝ × Space → ℝ≥0∞) (expChart p) =
      rhoE p * s.indicator (1 : ℝ × Space → ℝ≥0∞) (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)
    have hc : chartPsi τ₀ (expChart p) = (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) := by
      simp [chartPsi, expChart]
    by_cases h : (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) ∈ s
    · have h' : expChart p ∈ chartPsi τ₀ ⁻¹' s := by
        show chartPsi τ₀ (expChart p) ∈ s
        rw [hc]
        exact h
      simp only [Set.indicator_of_mem h', Set.indicator_of_mem h, Pi.one_apply]
    · have h' : expChart p ∉ chartPsi τ₀ ⁻¹' s := by
        show ¬ chartPsi τ₀ (expChart p) ∈ s
        rw [hc]
        exact h
      simp only [Set.indicator_of_notMem h', Set.indicator_of_notMem h, mul_zero]
  have hinv : ∀ p : ℝ × Space, dilChartInv (dilChart p) = p := fun p => by
    simp only [dilChart, dilChartInv, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      one_smul]
  have hterm : ∀ p : ℝ × Space,
      rhoD p * (rhoE p * s.indicator (1 : ℝ × Space → ℝ≥0∞) (τ₀ + p.1, p.2)) =
        ((fun p : ℝ × Space => (τ₀ + p.1, p.2)) ⁻¹' s).indicator
          (fun p => rhoD p * rhoE p) p := by
    intro p
    by_cases h : (τ₀ + p.1, p.2) ∈ s
    · have h' : p ∈ (fun p : ℝ × Space => (τ₀ + p.1, p.2)) ⁻¹' s := h
      simp only [Set.indicator_of_mem h', Set.indicator_of_mem h, Pi.one_apply, mul_one]
    · have h' : p ∉ (fun p : ℝ × Space => (τ₀ + p.1, p.2)) ⁻¹' s := h
      simp only [Set.indicator_of_notMem h', Set.indicator_of_notMem h, mul_zero]
  rw [Measure.map_apply hmeas hs, ← lintegral_indicator_one (hmeas hs),
    lintegral_expChart' ((chartPsi τ₀ ⁻¹' s).indicator (1 : ℝ × Space → ℝ≥0∞)),
    lintegral_congr key,
    lintegral_dilChart' (fun p : ℝ × Space =>
      (fun q : ℝ × Space => rhoE q * s.indicator (1 : ℝ × Space → ℝ≥0∞) (τ₀ + q.1, q.2))
        (dilChartInv p))]
  simp only [hinv]
  rw [lintegral_congr hterm, lintegral_indicator hTs]
  exact setLIntegral_measure_zero _ _ hT0

theorem chart_aesm {P : ℝ} {g : ℝ → SpatialField} (hg : B0005.IsY2 P g) (τ₀ : ℝ) (i : Fin 3) :
    AEStronglyMeasurable (fun X : ℝ × Space => chartField τ₀ g (Real.log X.1) X.2 i)
      (volume.restrict (Ioi (0:ℝ) ×ˢ (univ : Set Space))) := by
  have hcont : Continuous (fun v : Space => v i) := by fun_prop
  have hGi : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2 i) volume :=
    hcont.comp_aestronglyMeasurable hg.measurable
  have hlog : Measurable fun X : ℝ × Space => Real.log X.1 :=
    Real.measurable_log.comp measurable_fst
  have hexp : Measurable fun X : ℝ × Space => Real.exp (-(Real.log X.1 / 2)) :=
    Real.measurable_exp.comp (hlog.div_const 2).neg
  have e : (fun X : ℝ × Space => chartField τ₀ g (Real.log X.1) X.2 i) =
      fun X : ℝ × Space => Real.exp (-(Real.log X.1 / 2)) *
        (fun z : ℝ × Space => g z.1 z.2 i) (chartPsi τ₀ X) := by
    funext X
    simp [chartField, chartPsi, PiLp.smul_apply, smul_eq_mul]
  rw [e]
  exact hexp.aestronglyMeasurable.mul (hGi.comp_quasiMeasurePreserving (qmp_chartPsi τ₀))

/-! ## 4. The pointwise bound and the `L²` bound of one piece -/

theorem piece_pointwise {g : ℝ → SpatialField} (τ₀ : ℝ) (i : Fin 3) (a : ℝ → ℝ)
    (K : ℝ) (hK : ∀ t ∈ Ioo (-2:ℝ) 2, |a t| ≤ K) (hsupp : ∀ t, t ∉ Ioo (-2:ℝ) 2 → a t = 0)
    (p : ℝ × Space) :
    rhoD p * (rhoE (dilChart p) *
        ‖a (Real.log (expChart (dilChart p)).1) *
          chartField τ₀ g (Real.log (expChart (dilChart p)).1) (expChart (dilChart p)).2 i‖ₑ ^ 2) ≤
      ENNReal.ofReal (Real.exp 3 * K ^ 2) *
        ((Ioo (-2:ℝ) 2).indicator (1 : ℝ → ℝ≥0∞) p.1 * ‖g (τ₀ + p.1) p.2‖ₑ ^ 2) := by
  have hlog : Real.log (expChart (dilChart p)).1 = p.1 := by
    simp only [expChart, dilChart, Real.log_exp]
  have hc : chartField τ₀ g (Real.log (expChart (dilChart p)).1) (expChart (dilChart p)).2 i =
      Real.exp (-(p.1 / 2)) * g (τ₀ + p.1) p.2 i := by
    rw [hlog]
    simp only [expChart, dilChart]
    exact chart_dilChart τ₀ g i p
  rw [hc, hlog]
  have hE : Real.exp (-(p.1 / 2)) * Real.exp (-(p.1 / 2)) * Real.exp p.1 = 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
    congr 1
    ring
  have hL : rhoD p * (rhoE (dilChart p) *
      ‖a p.1 * (Real.exp (-(p.1 / 2)) * g (τ₀ + p.1) p.2 i)‖ₑ ^ 2) =
      ENNReal.ofReal (Real.exp (3 * p.1 / 2) * (Real.exp p.1 *
        (a p.1 * (Real.exp (-(p.1 / 2)) * g (τ₀ + p.1) p.2 i)) ^ 2)) := by
    simp only [rhoD, rhoE, dilChart]
    rw [enorm_sq_real, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [hL]
  by_cases ht : p.1 ∈ Ioo (-2:ℝ) 2
  · have hR : Real.exp (3 * p.1 / 2) * (Real.exp p.1 *
        (a p.1 * (Real.exp (-(p.1 / 2)) * g (τ₀ + p.1) p.2 i)) ^ 2) =
        Real.exp (3 * p.1 / 2) * (a p.1 ^ 2 * g (τ₀ + p.1) p.2 i ^ 2) := by
      linear_combination (Real.exp (3 * p.1 / 2) * a p.1 ^ 2 * g (τ₀ + p.1) p.2 i ^ 2) * hE
    rw [hR]
    have hGv : |g (τ₀ + p.1) p.2 i| ≤ ‖g (τ₀ + p.1) p.2‖ := by
      have h0 := PiLp.norm_apply_le (g (τ₀ + p.1) p.2) i
      rwa [Real.norm_eq_abs] at h0
    have h1 : Real.exp (3 * p.1 / 2) ≤ Real.exp 3 :=
      Real.exp_le_exp.2 (by linarith [ht.2])
    have h2 : a p.1 ^ 2 ≤ K ^ 2 :=
      sq_le_sq' (abs_le.1 (hK p.1 ht)).1 (abs_le.1 (hK p.1 ht)).2
    have h3 : g (τ₀ + p.1) p.2 i ^ 2 ≤ ‖g (τ₀ + p.1) p.2‖ ^ 2 :=
      sq_le_sq' (abs_le.1 hGv).1 (abs_le.1 hGv).2
    have key : Real.exp (3 * p.1 / 2) * (a p.1 ^ 2 * g (τ₀ + p.1) p.2 i ^ 2) ≤
        Real.exp 3 * (K ^ 2 * ‖g (τ₀ + p.1) p.2‖ ^ 2) :=
      mul_le_mul h1 (mul_le_mul h2 h3 (sq_nonneg _) (sq_nonneg _)) (by positivity)
        (Real.exp_pos _).le
    simp only [Set.indicator_of_mem ht, Pi.one_apply, one_mul]
    rw [enorm_sq_eq_ofReal_norm,
      ← ENNReal.ofReal_mul (show (0:ℝ) ≤ Real.exp 3 * K ^ 2 by positivity)]
    exact ENNReal.ofReal_le_ofReal (key.trans_eq (by ring))
  · rw [hsupp p.1 ht]
    simp

theorem piece_memLp {P : ℝ} (hP : 0 < P) {g : ℝ → SpatialField} (hg : B0005.IsY2 P g)
    (τ₀ : ℝ) (i : Fin 3) (a : ℝ → ℝ) (ha : Measurable a) (K : ℝ)
    (hK : ∀ t ∈ Ioo (-2:ℝ) 2, |a t| ≤ K) (hsupp : ∀ t, t ∉ Ioo (-2:ℝ) 2 → a t = 0) :
    MemLp (fun X : ℝ × Space =>
      if 0 < X.1 then a (Real.log X.1) * chartField τ₀ g (Real.log X.1) X.2 i else 0) 2 volume := by
  have hA : MeasurableSet (Ioi (0:ℝ) ×ˢ (univ : Set Space)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have ha' : Measurable (fun X : ℝ × Space => a (Real.log X.1)) :=
    ha.comp (Real.measurable_log.comp measurable_fst)
  have hFm : AEStronglyMeasurable
      (fun X : ℝ × Space => a (Real.log X.1) * chartField τ₀ g (Real.log X.1) X.2 i)
      (volume.restrict (Ioi (0:ℝ) ×ˢ (univ : Set Space))) :=
    ha'.aestronglyMeasurable.mul (chart_aesm hg τ₀ i)
  have hind : (fun X : ℝ × Space =>
      if 0 < X.1 then a (Real.log X.1) * chartField τ₀ g (Real.log X.1) X.2 i else 0) =
      (Ioi (0:ℝ) ×ˢ (univ : Set Space)).indicator
        (fun X : ℝ × Space => a (Real.log X.1) * chartField τ₀ g (Real.log X.1) X.2 i) := by
    funext X
    by_cases hX : 0 < X.1
    · have hXA : X ∈ Ioi (0:ℝ) ×ˢ (univ : Set Space) := ⟨hX, trivial⟩
      simp only [if_pos hX, Set.indicator_of_mem hXA]
    · have hXA : X ∉ Ioi (0:ℝ) ×ˢ (univ : Set Space) := fun h' => hX h'.1
      simp only [if_neg hX, Set.indicator_of_notMem hXA]
  have hsq : ∫⁻ X, ‖(Ioi (0:ℝ) ×ˢ (univ : Set Space)).indicator
        (fun X : ℝ × Space => a (Real.log X.1) * chartField τ₀ g (Real.log X.1) X.2 i) X‖ₑ ^ 2
      = ∫⁻ X in Ioi (0:ℝ) ×ˢ (univ : Set Space),
        ‖a (Real.log X.1) * chartField τ₀ g (Real.log X.1) X.2 i‖ₑ ^ 2 := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun X => ?_
    by_cases hX : X ∈ Ioi (0:ℝ) ×ˢ (univ : Set Space)
    · simp only [Set.indicator_of_mem hX]
    · simp [Set.indicator_of_notMem hX]
  have hmain : ∫⁻ X in Ioi (0:ℝ) ×ˢ (univ : Set Space),
        ‖a (Real.log X.1) * chartField τ₀ g (Real.log X.1) X.2 i‖ₑ ^ 2 ≤
      ∫⁻ p : ℝ × Space, ENNReal.ofReal (Real.exp 3 * K ^ 2) *
        ((Ioo (-2:ℝ) 2).indicator (1 : ℝ → ℝ≥0∞) p.1 * ‖g (τ₀ + p.1) p.2‖ₑ ^ 2) := by
    rw [lintegral_expChart' (fun X : ℝ × Space =>
        ‖a (Real.log X.1) * chartField τ₀ g (Real.log X.1) X.2 i‖ₑ ^ 2),
      lintegral_dilChart' (fun p : ℝ × Space =>
        rhoE p * ‖a (Real.log (expChart p).1) *
          chartField τ₀ g (Real.log (expChart p).1) (expChart p).2 i‖ₑ ^ 2)]
    exact lintegral_mono fun p => piece_pointwise τ₀ i a K hK hsupp p
  rw [hind]
  refine memLp_two_of_lintegral_sq ((aestronglyMeasurable_indicator_iff hA).2 hFm) ?_
  rw [hsq]
  refine lt_of_le_of_lt hmain ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (window_lintegral_lt_top hP hg τ₀)

/-! ## 5. The theorem `WindowChartL2` -/

theorem windowChartL2 : WindowChartL2 := by
  unfold WindowChartL2
  intro h μ P w f χ τ₀ i hP hw hf hχ
  have hχc : Continuous χ := hχ.smooth.continuous
  have hχm : Measurable χ := hχc.measurable
  obtain ⟨Kχ, hKχ⟩ := hχc.bounded_above_of_compact_support hχ.compact
  have hdc : Continuous (deriv χ) := by
    first
    | exact hχ.smooth.continuous_deriv (by simp)
    | exact hχ.smooth.continuous_deriv (by norm_num)
    | exact hχ.smooth.continuous_deriv le_top
  have hdm : Measurable (deriv χ) := hdc.measurable
  obtain ⟨Kd, hKd⟩ := hdc.bounded_above_of_compact_support hχ.compact.deriv
  have hχ0 : ∀ t, t ∉ Ioo (-2:ℝ) 2 → χ t = 0 := fun t ht => by
    by_contra hne
    exact ht (hχ.support (subset_tsupport χ (show t ∈ Function.support χ from hne)))
  have hd0 : ∀ t, t ∉ Ioo (-2:ℝ) 2 → deriv χ t = 0 := fun t ht => by
    by_contra hne
    exact ht (hχ.support (support_deriv_subset (show t ∈ Function.support (deriv χ) from hne)))
  have hχb : ∀ t, |χ t| ≤ Kχ := fun t => by
    have := hKχ t
    rwa [Real.norm_eq_abs] at this
  have hdb : ∀ t, |deriv χ t| ≤ Kd := fun t => by
    have := hKd t
    rwa [Real.norm_eq_abs] at this
  refine ⟨?_, ?_⟩
  · show MemLp (fun X : ℝ × Space =>
      if 0 < X.1 then χ (Real.log X.1) * chartField τ₀ w (Real.log X.1) X.2 i else 0) 2 volume
    exact piece_memLp hP hw τ₀ i χ hχm Kχ (fun t _ => hχb t) (fun t ht => hχ0 t ht)
  · have e : windowF χ μ τ₀ w f i = fun X : ℝ × Space =>
        (if 0 < X.1 then (-(Real.exp (-(Real.log X.1)) * χ (Real.log X.1))) *
            chartField τ₀ f (Real.log X.1) X.2 i else 0) +
        (if 0 < X.1 then (Real.exp (-(Real.log X.1)) *
            (-(μ * χ (Real.log X.1)) + deriv χ (Real.log X.1))) *
            chartField τ₀ w (Real.log X.1) X.2 i else 0) := by
      funext X
      by_cases hX : 0 < X.1
      · have hinv : X.1⁻¹ = Real.exp (-(Real.log X.1)) := by
          rw [Real.exp_neg, Real.exp_log hX]
        simp only [windowF, if_pos hX]
        rw [hinv]
        ring
      · simp only [windowF, if_neg hX, add_zero]
    have hmF : Measurable (fun t : ℝ => -(Real.exp (-t) * χ t)) :=
      ((Real.measurable_exp.comp measurable_neg).mul hχm).neg
    have hmW : Measurable (fun t : ℝ => Real.exp (-t) * (-(μ * χ t) + deriv χ t)) :=
      (Real.measurable_exp.comp measurable_neg).mul
        (((measurable_const.mul hχm).neg).add hdm)
    have hKF : ∀ t ∈ Ioo (-2:ℝ) 2, |-(Real.exp (-t) * χ t)| ≤ Real.exp 2 * Kχ := fun t ht => by
      rw [abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (Real.exp_le_exp.2 (by linarith [ht.1])) (hχb t) (abs_nonneg _)
        (Real.exp_pos _).le
    have hKW : ∀ t ∈ Ioo (-2:ℝ) 2,
        |Real.exp (-t) * (-(μ * χ t) + deriv χ t)| ≤ Real.exp 2 * (|μ| * Kχ + Kd) :=
      fun t ht => by
        have h1 : |μ * χ t| ≤ |μ| * Kχ := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hχb t) (abs_nonneg _)
        have h3 : |-(μ * χ t) + deriv χ t| ≤ |μ| * Kχ + Kd :=
          abs_le.2 ⟨by linarith [(abs_le.1 h1).1, (abs_le.1 h1).2, (abs_le.1 (hdb t)).1,
              (abs_le.1 (hdb t)).2],
            by linarith [(abs_le.1 h1).1, (abs_le.1 h1).2, (abs_le.1 (hdb t)).1,
              (abs_le.1 (hdb t)).2]⟩
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (Real.exp_le_exp.2 (by linarith [ht.1])) h3 (abs_nonneg _)
          (Real.exp_pos _).le
    have hsF : ∀ t, t ∉ Ioo (-2:ℝ) 2 → -(Real.exp (-t) * χ t) = 0 := fun t ht => by
      rw [hχ0 t ht]
      ring
    have hsW : ∀ t, t ∉ Ioo (-2:ℝ) 2 → Real.exp (-t) * (-(μ * χ t) + deriv χ t) = 0 :=
      fun t ht => by
        rw [hχ0 t ht, hd0 t ht]
        ring
    rw [e]
    exact (piece_memLp hP hf τ₀ i (fun t => -(Real.exp (-t) * χ t)) hmF (Real.exp 2 * Kχ)
        hKF hsF).add
      (piece_memLp hP hw τ₀ i (fun t => Real.exp (-t) * (-(μ * χ t) + deriv χ t)) hmW
        (Real.exp 2 * (|μ| * Kχ + Kd)) hKW hsW)

end UnforcedLeray.Short.Interface
