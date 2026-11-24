import UnforcedLeray.Lib.FreeStressCouplings.PhaseLaplacian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.Floor

/-!
# The flow chart of `B = T₀ - 3/4` on `(ℝ/Pℤ) × ℝ³` (INF10 F1, part B: measure theory)


§4 bypass **B9** and §5 Level F, target **F1**; blueprint unit **B0459** (tex 7698-7722).

`B = ∂_τ - y·∇/2 - 3/4` (tex 140, 7318, 7704-7706) generates the unitary group
`(e^{tB} w)(τ, y) = e^{-3t/4} w(τ + t, e^{-t/2} y)` (tex 7713-7715: phase translation composed
with the `L²`-normalised dilation).  Its orbits on `(ℝ/Pℤ) × (ℝ³ \ 0)` are straightened by the chart

  `Θ : ℝ × K → (ℝ/Pℤ) × ℝ³,  Θ(θ, z) = ([θ], e^{-θ/2} z)`,  `K = {1 ≤ |z| < e^{P/2}}`,

in which the flow is the translation `θ ↦ θ + t`.  `Θ` is a bijection onto
`(ℝ/Pℤ) × (ℝ³ \ 0)`: the shells `e^{-θ/2} K`, `θ ∈ [θ₀, θ₀ + P)`, tile `ℝ³ \ 0`.  The inverse is
`chartInv`, with `θ` the representative of the phase satisfying `e^{θ/2}|y| ∈ [1, e^{P/2})`.
This is the replacement for "Fourier series in `τ` and Mellin–Plancherel in `|y|`" of bypass
B9: a single Fourier transform in `θ` then diagonalises `B` (`PhaseDilation.lean`).

* `lintegral_chartFwd`: the change of variables
  `∫ J(θ)² F(Θ(θ, z)) dθ dz|_K = ∫ F d(haar × dy)` with `J(θ)² = e^{-3θ/2}/P`;
* `measurePreserving_chartFwd`, `measurePreserving_chartInv`: `Θ` and its inverse are measure
  preserving between `chartMeasure P = (dθ × dz|_K).withDensity J²` and `haar × dy`;
* `chartFwd_chartInv` (everywhere), `ae_chartInv_chartFwd` (a.e.).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real Module
open scoped ENNReal

namespace UnforcedLeray.FreeStress

open UnforcedLeray.PhaseSpace

variable (P : ℝ) [hP : Fact (0 < P)]

/-- The fundamental shell `K = {z : 1 ≤ |z| < e^{P/2}}`. -/
def shell : Set Space := {z | 1 ≤ ‖z‖ ∧ ‖z‖ < Real.exp (P / 2)}

theorem measurableSet_shell : MeasurableSet (shell P) :=
  (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

/-- The chart `Θ(θ, z) = ([θ], e^{-θ/2} z)`. -/
def chartFwd (p : ℝ × Space) : AddCircle P × Space :=
  ((p.1 : AddCircle P), Real.exp (-(p.1 / 2)) • p.2)

theorem measurable_chartFwd : Measurable (chartFwd P) := by
  unfold chartFwd
  fun_prop

/-- The representative in `[0, P)` of a phase. -/
def phaseRep (τ : AddCircle P) : ℝ := (AddCircle.equivIco P 0 τ : ℝ)

theorem measurable_phaseRep : Measurable (phaseRep P) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco P 0).measurable

theorem coe_phaseRep (τ : AddCircle P) : ((phaseRep P τ : ℝ) : AddCircle P) = τ :=
  AddCircle.coe_equivIco

/-- The chart coordinate `θ(τ, y)`: the representative of `τ` with `e^{θ/2}|y| ∈ [1, e^{P/2})`
(for `y ≠ 0`). -/
def chartTheta (q : AddCircle P × Space) : ℝ :=
  phaseRep P q.1 - P * ⌊(phaseRep P q.1 + 2 * Real.log ‖q.2‖) / P⌋

/-- The inverse chart `(τ, y) ↦ (θ, e^{θ/2} y)`. -/
def chartInv (q : AddCircle P × Space) : ℝ × Space :=
  (chartTheta P q, Real.exp (chartTheta P q / 2) • q.2)

theorem measurable_chartTheta : Measurable (chartTheta P) := by
  unfold chartTheta
  have h1 : Measurable fun q : AddCircle P × Space => phaseRep P q.1 :=
    (measurable_phaseRep P).comp measurable_fst
  have h2 : Measurable fun q : AddCircle P × Space =>
      (phaseRep P q.1 + 2 * Real.log ‖q.2‖) / P := by
    refine (h1.add (measurable_const.mul ?_)).div_const _
    exact Real.measurable_log.comp (measurable_norm.comp measurable_snd)
  exact h1.sub (measurable_const.mul
    ((Measurable.of_discrete (f := (Int.cast : ℤ → ℝ))).comp (Int.measurable_floor.comp h2)))

theorem measurable_chartInv : Measurable (chartInv P) := by
  unfold chartInv
  have h := measurable_chartTheta P
  refine h.prodMk ?_
  exact (Real.measurable_exp.comp (h.div_const 2)).smul measurable_snd

theorem coe_chartTheta (q : AddCircle P × Space) : ((chartTheta P q : ℝ) : AddCircle P) = q.1 := by
  unfold chartTheta
  rw [AddCircle.coe_sub, coe_phaseRep, sub_eq_self, AddCircle.coe_eq_zero_iff]
  exact ⟨⌊(phaseRep P q.1 + 2 * Real.log ‖q.2‖) / P⌋, by rw [zsmul_eq_mul, mul_comm]⟩

/-- `Θ ∘ Θ⁻¹ = id` everywhere. -/
theorem chartFwd_chartInv (q : AddCircle P × Space) : chartFwd P (chartInv P q) = q := by
  obtain ⟨τ, y⟩ := q
  refine Prod.ext (coe_chartTheta P (τ, y)) ?_
  change Real.exp (-(chartTheta P (τ, y) / 2)) • Real.exp (chartTheta P (τ, y) / 2) • y = y
  rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

/-- `Θ⁻¹ ∘ Θ = id` on `ℝ × K`. -/
theorem chartInv_chartFwd {θ : ℝ} {z : Space} (hz : z ∈ shell P) :
    chartInv P (chartFwd P (θ, z)) = (θ, z) := by
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz.1
  have hl0 : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hz.1
  have hl1 : Real.log ‖z‖ < P / 2 := (Real.log_lt_iff_lt_exp hz0).2 hz.2
  set t := phaseRep P (θ : AddCircle P) with ht_def
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m • P = θ - t := by
    rw [← AddCircle.coe_eq_zero_iff, AddCircle.coe_sub, ht_def, coe_phaseRep, sub_self]
  rw [zsmul_eq_mul] at hm
  have hlog : Real.log ‖Real.exp (-(θ / 2)) • z‖ = -(θ / 2) + Real.log ‖z‖ := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.log_mul (Real.exp_pos _).ne' hz0.ne', Real.log_exp]
  have hθ : chartTheta P (chartFwd P (θ, z)) = θ := by
    have hP0 : P ≠ 0 := hP.out.ne'
    have key : (t + 2 * Real.log ‖Real.exp (-(θ / 2)) • z‖) / P =
        2 * Real.log ‖z‖ / P - (m : ℝ) := by
      rw [hlog]
      field_simp
      linarith
    have hfl : ⌊2 * Real.log ‖z‖ / P⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]
      constructor
      · exact div_nonneg (by linarith) hP.out.le
      · rw [div_lt_one hP.out]
        linarith
    change t - P * ⌊(t + 2 * Real.log ‖Real.exp (-(θ / 2)) • z‖) / P⌋ = θ
    rw [key, Int.floor_sub_intCast, hfl]
    push_cast
    linarith
  change (chartTheta P (chartFwd P (θ, z)),
    Real.exp (chartTheta P (chartFwd P (θ, z)) / 2) • Real.exp (-(θ / 2)) • z) = (θ, z)
  rw [hθ, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

/-- For `y ≠ 0`: `e^{θ/2} y ∈ K` iff `θ ∈ [-2 log|y|, -2 log|y| + P)`. -/
theorem smul_mem_shell_iff {y : Space} (hy : y ≠ 0) (θ : ℝ) :
    Real.exp (θ / 2) • y ∈ shell P ↔
      θ ∈ Ico (-2 * Real.log ‖y‖) (-2 * Real.log ‖y‖ + P) := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hnorm : ‖Real.exp (θ / 2) • y‖ = Real.exp (θ / 2 + Real.log ‖y‖) := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_add, Real.exp_log hn]
  simp only [shell, mem_ofPred_eq, hnorm, mem_Ico, Real.one_le_exp_iff, Real.exp_lt_exp]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- The normalising factor `J(θ) = e^{-3θ/4} / √P` of the chart. -/
def chartJ (θ : ℝ) : ℝ := Real.exp (-(3 / 4) * θ) * (Real.sqrt P)⁻¹

theorem chartJ_pos (θ : ℝ) : 0 < chartJ P θ :=
  mul_pos (Real.exp_pos _) (inv_pos.2 (Real.sqrt_pos.2 hP.out))

theorem measurable_chartJ : Measurable (chartJ P) := by
  unfold chartJ
  fun_prop

theorem chartJ_sq (θ : ℝ) : chartJ P θ ^ 2 = Real.exp (-(3 / 2) * θ) / P := by
  unfold chartJ
  rw [mul_pow, inv_pow, Real.sq_sqrt hP.out.le, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- The base measure `dθ × dz|_K` of the chart. -/
abbrev chartBase : Measure (ℝ × Space) :=
  (volume : Measure ℝ).prod (volume.restrict (shell P))

/-- The chart measure `J(θ)² dθ dz|_K`, the pull-back of `haar × dy` by `Θ`. -/
def chartMeasure : Measure (ℝ × Space) :=
  (chartBase P).withDensity fun p => ENNReal.ofReal (chartJ P p.1 ^ 2)

/-- The set `{(θ, y) : e^{θ/2} y ∈ K}`. -/
def chartSet : Set (ℝ × Space) := {p | Real.exp (p.1 / 2) • p.2 ∈ shell P}

theorem measurableSet_chartSet : MeasurableSet (chartSet P) := by
  have h : Measurable fun p : ℝ × Space => Real.exp (p.1 / 2) • p.2 := by fun_prop
  exact h (measurableSet_shell P)

/-- The inner integral after the dilation `z = e^{θ/2} y`. -/
theorem lintegral_shell_dilate {F : AddCircle P × Space → ℝ≥0∞} (hF : Measurable F) (θ : ℝ) :
    ∫⁻ z in shell P, ENNReal.ofReal (chartJ P θ ^ 2) * F (chartFwd P (θ, z)) =
      ENNReal.ofReal P⁻¹ * ∫⁻ y, (chartSet P).indicator
        (fun p => F ((p.1 : AddCircle P), p.2)) (θ, y) := by
  set r : ℝ := Real.exp (-(θ / 2)) with hr
  have hr0 : r ≠ 0 := (Real.exp_pos _).ne'
  set H : Space → ℝ≥0∞ := fun y => ENNReal.ofReal (chartJ P θ ^ 2) *
    (chartSet P).indicator (fun p => F ((p.1 : AddCircle P), p.2)) (θ, y) with hH
  have hHm : Measurable H := by
    refine measurable_const.mul ?_
    refine ((Measurable.indicator ?_ (measurableSet_chartSet P))).comp measurable_prodMk_left
    exact hF.comp (by fun_prop)
  have hpt : ∀ z, (shell P).indicator
      (fun z => ENNReal.ofReal (chartJ P θ ^ 2) * F (chartFwd P (θ, z))) z = H (r • z) := by
    intro z
    have hz : Real.exp (θ / 2) • r • z = z := by
      rw [hr, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
    by_cases hzK : z ∈ shell P
    · rw [indicator_of_mem hzK, hH]
      simp only
      rw [indicator_of_mem (show ((θ, r • z) : ℝ × Space) ∈ chartSet P from by
        change Real.exp (θ / 2) • r • z ∈ shell P
        rw [hz]
        exact hzK)]
      rfl
    · rw [indicator_of_notMem hzK, hH]
      simp only
      rw [indicator_of_notMem (show ((θ, r • z) : ℝ × Space) ∉ chartSet P from by
        change ¬ Real.exp (θ / 2) • r • z ∈ shell P
        rw [hz]
        exact hzK), mul_zero]
  rw [← lintegral_indicator (measurableSet_shell P)]
  simp_rw [hpt]
  rw [← lintegral_map hHm (measurable_const_smul r), Measure.map_addHaar_smul volume hr0,
    lintegral_smul_measure]
  simp only [hH]
  rw [lintegral_const_mul (f := fun y => (chartSet P).indicator
      (fun p => F ((p.1 : AddCircle P), p.2)) (θ, y)) _ (((Measurable.indicator
      (hF.comp (by fun_prop)) (measurableSet_chartSet P))).comp measurable_prodMk_left),
    finrank_euclideanSpace_fin, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 2
  rw [chartJ_sq, hr, ← Real.exp_nat_mul, abs_of_pos (inv_pos.2 (Real.exp_pos _))]
  have e : ((3 : ℕ) : ℝ) * -(θ / 2) = -(3 / 2) * θ := by push_cast; ring
  rw [e]
  have hE : Real.exp (-(3 / 2) * θ) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- **Change of variables for the flow chart**:
`∫ J(θ)² F(Θ(θ, z)) dθ dz|_K = ∫ F d(haar × dy)` for measurable `F ≥ 0`. -/
theorem lintegral_chartFwd {F : AddCircle P × Space → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, ENNReal.ofReal (chartJ P p.1 ^ 2) * F (chartFwd P p) ∂(chartBase P) =
      ∫⁻ q, F q ∂(phaseVol P) := by
  have hmeas : Measurable fun p : ℝ × Space =>
      ENNReal.ofReal (chartJ P p.1 ^ 2) * F (chartFwd P p) :=
    (ENNReal.measurable_ofReal.comp (((measurable_chartJ P).comp measurable_fst).pow_const 2)).mul
      (hF.comp (measurable_chartFwd P))
  set G : ℝ × Space → ℝ≥0∞ := (chartSet P).indicator (fun p => F ((p.1 : AddCircle P), p.2))
    with hG
  have hGm : Measurable G :=
    Measurable.indicator (hF.comp (by fun_prop)) (measurableSet_chartSet P)
  rw [lintegral_prod _ hmeas.aemeasurable]
  simp_rw [lintegral_shell_dilate P hF]
  rw [lintegral_const_mul _ hGm.lintegral_prod_right',
    lintegral_lintegral_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space))
      (f := fun θ y => G (θ, y)) hGm.aemeasurable]
  have hy0 : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
    rw [ae_iff]
    simpa using (measure_singleton (0 : Space) : volume ({0} : Set Space) = 0)
  have hinner : ∀ y : Space, y ≠ 0 → ∫⁻ θ, G (θ, y) =
      ENNReal.ofReal P * ∫⁻ τ, F (τ, y) ∂(AddCircle.haarAddCircle (T := P)) := by
    intro y hy
    set a := -2 * Real.log ‖y‖
    have hset : (fun θ => G (θ, y)) =
        (Ico a (a + P)).indicator (fun θ => F ((θ : AddCircle P), y)) := by
      funext θ
      by_cases hθ : θ ∈ Ico a (a + P)
      · rw [indicator_of_mem hθ, hG, indicator_of_mem]
        exact (smul_mem_shell_iff P hy θ).2 hθ
      · rw [indicator_of_notMem hθ, hG, indicator_of_notMem]
        exact fun h => hθ ((smul_mem_shell_iff P hy θ).1 h)
    rw [hset, lintegral_indicator measurableSet_Ico, setLIntegral_congr Ico_ae_eq_Ioc,
      AddCircle.lintegral_preimage P a (fun τ => F (τ, y)), AddCircle.volume_eq_smul_haarAddCircle,
      lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_congr_ae (g := fun y => ENNReal.ofReal P *
    ∫⁻ τ, F (τ, y) ∂(AddCircle.haarAddCircle (T := P))) (by
      filter_upwards [hy0] with y hy using hinner y hy)]
  rw [lintegral_const_mul _ ?_, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hP.out.le),
    inv_mul_cancel₀ hP.out.ne', ENNReal.ofReal_one, one_mul, lintegral_prod_symm' _ hF]
  exact hF.lintegral_prod_left'

/-- **`Θ` is measure preserving** from the chart measure to `haar × dy`. -/
theorem measurePreserving_chartFwd :
    MeasurePreserving (chartFwd P) (chartMeasure P) (phaseVol P) := by
  refine ⟨measurable_chartFwd P, ?_⟩
  ext s hs
  have hpre : MeasurableSet (chartFwd P ⁻¹' s) := measurable_chartFwd P hs
  rw [Measure.map_apply (measurable_chartFwd P) hs, chartMeasure, withDensity_apply _ hpre,
    ← lintegral_indicator hpre, ← lintegral_indicator_one hs,
    ← lintegral_chartFwd P (measurable_one.indicator hs)]
  refine lintegral_congr fun p => ?_
  by_cases hp : chartFwd P p ∈ s
  · rw [indicator_of_mem (show p ∈ chartFwd P ⁻¹' s from hp), indicator_of_mem hp, Pi.one_apply,
      mul_one]
  · rw [indicator_of_notMem (show p ∉ chartFwd P ⁻¹' s from hp), indicator_of_notMem hp,
      mul_zero]

theorem ae_mem_shell : ∀ᵐ p ∂(chartMeasure P), p.2 ∈ shell P := by
  have h : ∀ᵐ p ∂(chartBase P), p.2 ∈ shell P := by
    rw [Measure.ae_prod_iff_ae_ae (measurable_snd (measurableSet_shell P))]
    exact Eventually.of_forall fun _ => ae_restrict_mem (measurableSet_shell P)
  exact (withDensity_absolutelyContinuous _ _).ae_le h

/-- `Θ⁻¹ ∘ Θ = id` almost everywhere for the chart measure. -/
theorem ae_chartInv_chartFwd : ∀ᵐ p ∂(chartMeasure P), chartInv P (chartFwd P p) = p := by
  filter_upwards [ae_mem_shell P] with p hp
  exact chartInv_chartFwd P hp

/-- **`Θ⁻¹` is measure preserving** from `haar × dy` to the chart measure. -/
theorem measurePreserving_chartInv :
    MeasurePreserving (chartInv P) (phaseVol P) (chartMeasure P) := by
  refine ⟨measurable_chartInv P, ?_⟩
  rw [← (measurePreserving_chartFwd P).map_eq,
    Measure.map_map (measurable_chartInv P) (measurable_chartFwd P),
    Measure.map_congr (g := id) (by
      filter_upwards [ae_chartInv_chartFwd P] with p hp using hp), Measure.map_id]

/-- The chart base and the chart measure have the same null sets. -/
theorem chartBase_ac : chartBase P ≪ chartMeasure P :=
  withDensity_absolutelyContinuous'
    ((ENNReal.measurable_ofReal.comp
      (((measurable_chartJ P).comp measurable_fst).pow_const 2))).aemeasurable
    (Eventually.of_forall fun p => by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos (chartJ_pos P p.1) 2)

theorem chartMeasure_ac : chartMeasure P ≪ chartBase P :=
  withDensity_absolutelyContinuous _ _

end UnforcedLeray.FreeStress
