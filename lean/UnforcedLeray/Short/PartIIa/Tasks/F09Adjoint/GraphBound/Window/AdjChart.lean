import UnforcedLeray.Units.B0424.Chart
import UnforcedLeray.Lib.Parabolic.Kernel

/-!
# Part II-a, task `PartII-a:F09/3/1/3/1`: the reversed window chart

Source `the November 2 reference manuscript`,
lines 1431-1441 (`θ = 1 - e^{-t}`, `x = e^{-t/2} y`).

The chart `Ψ(t, y) = (1 - e^{-t}, e^{-t/2} y)` maps `ℝ × ℝ³` onto `{θ < 1}` with Jacobian
`e^{-t} · e^{-3t/2} = e^{-5t/2}`. It is factored as the spatial dilation inverse
`(t, y) ↦ (t, e^{-t/2} y)` (`dilChartInv`, Jacobian `e^{-3t/2}`), the time flip `t ↦ -t`
(measure preserving), the time change `E(s, x) = (e^s, x)` restricted to `s > 0` (`expChart`,
Jacobian `e^s`), and the reflection `(σ, x) ↦ (1 - σ, x)` (measure preserving). The Lebesgue and
Bochner forms are proved along this chain, with the primed chart lemmas of `Units/B0424/Chart.lean`
for the two non-linear steps.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Parabolic UnforcedLeray.B0424

/-! ### Measure-preserving helper maps on `ℝ × Space` -/

/-- The reflection `(σ, x) ↦ (1 - σ, x)` as a measurable equivalence. -/
def adjcRefl : (ℝ × Space) ≃ᵐ (ℝ × Space) where
  toFun p := (1 - p.1, p.2)
  invFun p := (1 - p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := Measurable.prodMk (measurable_const.sub measurable_fst) measurable_snd
  measurable_invFun := Measurable.prodMk (measurable_const.sub measurable_fst) measurable_snd

/-- The time flip `(t, x) ↦ (-t, x)` as a measurable equivalence. -/
def adjcNeg : (ℝ × Space) ≃ᵐ (ℝ × Space) where
  toFun p := (-p.1, p.2)
  invFun p := (-p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := Measurable.prodMk measurable_fst.neg measurable_snd
  measurable_invFun := Measurable.prodMk measurable_fst.neg measurable_snd

theorem adjcRefl_mp : MeasurePreserving adjcRefl volume volume := by
  rw [Measure.volume_eq_prod]
  exact (Measure.measurePreserving_sub_left volume (1 : ℝ)).prod (MeasurePreserving.id volume)

theorem adjcNeg_mp : MeasurePreserving adjcNeg volume volume := by
  rw [Measure.volume_eq_prod]
  exact (Measure.measurePreserving_neg volume).prod (MeasurePreserving.id volume)

/-! ### The spatial dilation inverse `(t, y) ↦ (t, e^{-t/2} y)` -/

theorem adjc_dilChart_fst (p : ℝ × Space) : (dilChart p).1 = p.1 := rfl

theorem adjc_dilChartInv_dilChart (p : ℝ × Space) : dilChartInv (dilChart p) = p := by
  simp only [dilChart, dilChartInv, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
    one_smul]

/-- Bochner form: `∫ k = ∫ e^{-3t/2} k(t, e^{-t/2} y)`. -/
theorem adjc_integral_dilInv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℝ × Space → E) :
    ∫ p, k p = ∫ q, Real.exp (-(3 * q.1 / 2)) • k (dilChartInv q) := by
  have h := integral_dilChart (fun q : ℝ × Space => Real.exp (-(3 * q.1 / 2)) • k (dilChartInv q))
  symm
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only
  rw [adjc_dilChart_fst, adjc_dilChartInv_dilChart, smul_smul, ← Real.exp_add,
    show 3 * p.1 / 2 + -(3 * p.1 / 2) = 0 by ring, Real.exp_zero, one_smul]

/-- Integrability form of `adjc_integral_dilInv`. -/
theorem adjc_integrable_dilInv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℝ × Space → E) :
    Integrable k ↔ Integrable (fun q : ℝ × Space => Real.exp (-(3 * q.1 / 2)) • k (dilChartInv q)) := by
  rw [integrable_dilChart_iff (fun q : ℝ × Space => Real.exp (-(3 * q.1 / 2)) • k (dilChartInv q))]
  refine integrable_congr (Eventually.of_forall fun p => ?_)
  dsimp only
  rw [adjc_dilChart_fst, adjc_dilChartInv_dilChart, smul_smul, ← Real.exp_add,
    show 3 * p.1 / 2 + -(3 * p.1 / 2) = 0 by ring, Real.exp_zero, one_smul]

/-- Lower-integral form: `∫⁻ G = ∫⁻ e^{-3t/2} G(t, e^{-t/2} y)`. -/
theorem adjc_lintegral_dilInv (G : ℝ × Space → ℝ≥0∞) :
    ∫⁻ p, G p = ∫⁻ q, ENNReal.ofReal (Real.exp (-(3 * q.1 / 2))) * G (dilChartInv q) := by
  have h := lintegral_dilChart'
    (fun q : ℝ × Space => ENNReal.ofReal (Real.exp (-(3 * q.1 / 2))) * G (dilChartInv q))
  rw [h]
  refine lintegral_congr fun p => ?_
  simp only [rhoD]
  rw [adjc_dilChart_fst, adjc_dilChartInv_dilChart, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos (3 * p.1 / 2)).le, ← Real.exp_add,
    show 3 * p.1 / 2 + -(3 * p.1 / 2) = 0 by ring, Real.exp_zero, ENNReal.ofReal_one, one_mul]

/-! ### Algebra of the weights -/

theorem adjc_smul_chain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ) (v : E) :
    Real.exp (-(3 * t / 2)) • (Real.exp (-t) • v) = Real.exp (-(5 * t / 2)) • v := by
  have h : -(3 * t / 2) + -t = -(5 * t / 2) := by ring
  rw [smul_smul, ← Real.exp_add, h]

theorem adjc_ennreal_chain (t : ℝ) (v : ℝ≥0∞) :
    ENNReal.ofReal (Real.exp (-(3 * t / 2))) * (ENNReal.ofReal (Real.exp (-t)) * v) =
      ENNReal.ofReal (Real.exp (-(5 * t / 2))) * v := by
  have h : -(3 * t / 2) + -t = -(5 * t / 2) := by ring
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos (-(3 * t / 2))).le, ← Real.exp_add, h]

/-! ### Support of the reflected function -/

theorem adjc_zero_off {E : Type*} [Zero E] (G : PS 3 → E)
    (hG : ∀ X : PS 3, 1 ≤ X.1 → G X = 0) (Y : ℝ × Space)
    (hY : Y ∉ Ioi (0 : ℝ) ×ˢ (univ : Set Space)) : G (1 - Y.1, Y.2) = 0 := by
  apply hG
  have h0 : ¬ (0 < Y.1) := fun h => hY ⟨h, mem_univ _⟩
  show (1 : ℝ) ≤ 1 - Y.1
  linarith [not_lt.mp h0]

theorem adjc_support_sub {E : Type*} [Zero E] (G : PS 3 → E)
    (hG : ∀ X : PS 3, 1 ≤ X.1 → G X = 0) :
    Function.support (fun Y : ℝ × Space => G (1 - Y.1, Y.2)) ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set Space) :=
  fun Y hY => by_contra fun h => (Function.mem_support.1 hY) (adjc_zero_off G hG Y h)

/-! ### The chart identities -/

/-- **Bochner form of the reversed chart.** -/
theorem integral_adjChart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : PS 3 → E)
    (hG : ∀ X : PS 3, 1 ≤ X.1 → G X = 0) :
    ∫ X, G X = ∫ p : ℝ × Space, Real.exp (-(5 * p.1 / 2)) • G (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) := by
  have s1 : ∫ X, G X = ∫ Y : ℝ × Space, G (1 - Y.1, Y.2) :=
    (adjcRefl_mp.integral_comp' G).symm
  have s2 : ∫ Y : ℝ × Space, G (1 - Y.1, Y.2) =
      ∫ Y in Ioi (0 : ℝ) ×ˢ (univ : Set Space), G (1 - Y.1, Y.2) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun Y hY => adjc_zero_off G hG Y hY)).symm
  have s3 := integral_expChart (fun Y : ℝ × Space => G (1 - Y.1, Y.2))
  have s4 : ∫ p : ℝ × Space, Real.exp p.1 • G (1 - (expChart p).1, (expChart p).2) =
      ∫ p : ℝ × Space, Real.exp (-p.1) • G (1 - Real.exp (-p.1), p.2) :=
    (adjcNeg_mp.integral_comp' (fun p : ℝ × Space =>
      Real.exp p.1 • G (1 - (expChart p).1, (expChart p).2))).symm
  have s5 := adjc_integral_dilInv
    (fun p : ℝ × Space => Real.exp (-p.1) • G (1 - Real.exp (-p.1), p.2))
  refine s1.trans (s2.trans (s3.trans (s4.trans (s5.trans ?_))))
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  dsimp only
  show Real.exp (-(3 * q.1 / 2)) • (Real.exp (-q.1) • G (1 - Real.exp (-q.1), Real.exp (-(q.1 / 2)) • q.2))
    = Real.exp (-(5 * q.1 / 2)) • G (1 - Real.exp (-q.1), Real.exp (-(q.1 / 2)) • q.2)
  exact adjc_smul_chain q.1 _

/-- **Integrability through the reversed chart.** -/
theorem integrable_adjChart_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : PS 3 → E)
    (hG : ∀ X : PS 3, 1 ≤ X.1 → G X = 0) :
    Integrable G ↔ Integrable (fun p : ℝ × Space =>
      Real.exp (-(5 * p.1 / 2)) • G (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2)) := by
  have e1 : Integrable G ↔ Integrable (fun Y : ℝ × Space => G (1 - Y.1, Y.2)) :=
    (adjcRefl_mp.integrable_comp_emb adjcRefl.measurableEmbedding).symm
  have e2 : Integrable (fun Y : ℝ × Space => G (1 - Y.1, Y.2)) ↔
      IntegrableOn (fun Y : ℝ × Space => G (1 - Y.1, Y.2)) (Ioi (0 : ℝ) ×ˢ (univ : Set Space)) :=
    (integrableOn_iff_integrable_of_support_subset (adjc_support_sub G hG)).symm
  have e3 := integrable_expChart_iff (fun Y : ℝ × Space => G (1 - Y.1, Y.2))
  have e4 := adjcNeg_mp.integrable_comp_emb adjcNeg.measurableEmbedding
    (g := fun p : ℝ × Space => Real.exp p.1 • G (1 - (expChart p).1, (expChart p).2))
  have e5 := adjc_integrable_dilInv
    (fun p : ℝ × Space => Real.exp (-p.1) • G (1 - Real.exp (-p.1), p.2))
  refine e1.trans (e2.trans (e3.trans (e4.symm.trans (e5.trans ?_))))
  refine integrable_congr (Eventually.of_forall fun q => ?_)
  dsimp only
  show Real.exp (-(3 * q.1 / 2)) • (Real.exp (-q.1) • G (1 - Real.exp (-q.1), Real.exp (-(q.1 / 2)) • q.2))
    = Real.exp (-(5 * q.1 / 2)) • G (1 - Real.exp (-q.1), Real.exp (-(q.1 / 2)) • q.2)
  exact adjc_smul_chain q.1 _

/-- **Lower-integral form of the reversed chart** (no measurability hypothesis). -/
theorem lintegral_adjChart (G : PS 3 → ℝ≥0∞) (hG : ∀ X : PS 3, 1 ≤ X.1 → G X = 0) :
    ∫⁻ X, G X = ∫⁻ p : ℝ × Space, ENNReal.ofReal (Real.exp (-(5 * p.1 / 2))) *
      G (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) := by
  have s1 : ∫⁻ X, G X = ∫⁻ Y : ℝ × Space, G (1 - Y.1, Y.2) :=
    (adjcRefl_mp.lintegral_comp_emb adjcRefl.measurableEmbedding G).symm
  have s2 : ∫⁻ Y : ℝ × Space, G (1 - Y.1, Y.2) =
      ∫⁻ Y in Ioi (0 : ℝ) ×ˢ (univ : Set Space), G (1 - Y.1, Y.2) :=
    (setLIntegral_eq_of_support_subset (adjc_support_sub G hG)).symm
  have s3 := lintegral_expChart' (fun Y : ℝ × Space => G (1 - Y.1, Y.2))
  have s4 : ∫⁻ p : ℝ × Space, rhoE p * G (1 - (expChart p).1, (expChart p).2) =
      ∫⁻ p : ℝ × Space, ENNReal.ofReal (Real.exp (-p.1)) * G (1 - Real.exp (-p.1), p.2) :=
    (adjcNeg_mp.lintegral_comp_emb adjcNeg.measurableEmbedding
      (fun p : ℝ × Space => rhoE p * G (1 - (expChart p).1, (expChart p).2))).symm
  have s5 := adjc_lintegral_dilInv
    (fun q : ℝ × Space => ENNReal.ofReal (Real.exp (-q.1)) * G (1 - Real.exp (-q.1), q.2))
  refine s1.trans (s2.trans (s3.trans (s4.trans (s5.trans ?_))))
  refine lintegral_congr fun q => ?_
  show ENNReal.ofReal (Real.exp (-(3 * q.1 / 2))) *
      (ENNReal.ofReal (Real.exp (-q.1)) * G (1 - Real.exp (-q.1), Real.exp (-(q.1 / 2)) • q.2)) =
    ENNReal.ofReal (Real.exp (-(5 * q.1 / 2))) * G (1 - Real.exp (-q.1), Real.exp (-(q.1 / 2)) • q.2)
  exact adjc_ennreal_chain q.1 _

/-! ### Measurability and quasi-measure preservation of the chart -/

theorem adjc_measurable_chart :
    Measurable (fun p : ℝ × Space => ((1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) : PS 3)) := by
  fun_prop

/-- Null sets pull back to null sets under the chart. -/
theorem adjc_null (t : Set (PS 3)) (ht : MeasurableSet t) (h0 : volume t = 0) :
    volume ((fun p : ℝ × Space => ((1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) : PS 3)) ⁻¹' t)
      = 0 := by
  set s : Set (PS 3) := t ∩ {X : PS 3 | X.1 < 1} with hs_def
  have hs : MeasurableSet s := ht.inter (measurableSet_lt measurable_fst measurable_const)
  set G : PS 3 → ℝ≥0∞ := s.indicator 1 with hG_def
  have hG : ∀ X : PS 3, 1 ≤ X.1 → G X = 0 := by
    intro X hX
    apply Set.indicator_of_notMem
    intro hmem
    exact absurd (show X.1 < 1 from hmem.2) (not_lt.2 hX)
  have hlint : ∫⁻ X, G X = 0 := by
    have : ∫⁻ X, G X = volume s := lintegral_indicator_one hs
    rw [this]
    exact measure_mono_null Set.inter_subset_left h0
  have key := lintegral_adjChart G hG
  rw [hlint] at key
  have hmeasH : Measurable (fun p : ℝ × Space =>
      ENNReal.ofReal (Real.exp (-(5 * p.1 / 2))) *
        G (((1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) : PS 3))) :=
    Measurable.mul
      (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun p : ℝ × Space =>
        Real.exp (-(5 * p.1 / 2))))
      ((measurable_one.indicator hs).comp adjc_measurable_chart)
  have hae := (lintegral_eq_zero_iff hmeasH).1 key.symm
  have hz := ae_iff.1 hae
  refine measure_mono_null ?_ hz
  intro p hp
  have hlt : (1 - Real.exp (-p.1)) < 1 := by linarith [Real.exp_pos (-p.1)]
  have hGp : G ((1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) : PS 3) = 1 :=
    Set.indicator_of_mem (show ((1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) : PS 3) ∈ s from
      ⟨hp, hlt⟩) (1 : PS 3 → ℝ≥0∞)
  show ¬ (ENNReal.ofReal (Real.exp (-(5 * p.1 / 2))) *
      G ((1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) : PS 3) = 0)
  rw [hGp, mul_one]
  exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

/-- **Quasi-measure preservation of the reversed chart.** -/
theorem adjChart_qmp :
    Measure.QuasiMeasurePreserving
      (fun p : ℝ × Space => ((1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) : PS 3))
      volume volume := by
  refine ⟨adjc_measurable_chart, ?_⟩
  intro s hs0
  obtain ⟨t, hst, htm, ht0⟩ := exists_measurable_superset_of_null hs0
  apply measure_mono_null hst
  rw [Measure.map_apply adjc_measurable_chart htm]
  exact adjc_null t htm ht0

end UnforcedLeray.Short.PartIIa
