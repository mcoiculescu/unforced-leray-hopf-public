import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.Defs
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Ball average of `G` at radius `r` about `y`, as in `hlMax`. -/
def termR (G : Space → ℝ≥0∞) (r : ℝ) (y : Space) : ℝ≥0∞ :=
  (volume (ball y r))⁻¹ * ∫⁻ z in ball y r, G z

/-- The function `(y, z) ↦ G(z) 1_{|z - y| < r}`. -/
def ballInd (G : Space → ℝ≥0∞) (r : ℝ) : Space × Space → ℝ≥0∞ :=
  fun p => {p : Space × Space | dist p.2 p.1 < r}.indicator (fun p => G p.2) p

lemma ballInd_eq (G : Space → ℝ≥0∞) (r : ℝ) (y z : Space) :
    ballInd G r (y, z) = (ball y r).indicator G z := by
  classical
  simp [ballInd, Set.indicator_apply, mem_ball]

lemma termR_measurable (G : Space → ℝ≥0∞) (hG : Measurable G) (r : ℝ) :
    Measurable (fun y => termR G r y) := by
  have hSet : MeasurableSet {p : Space × Space | dist p.2 p.1 < r} :=
    (isOpen_lt (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  have hF : Measurable (ballInd G r) :=
    (hG.comp measurable_snd).indicator hSet
  have hint : ∀ y : Space, ∫⁻ z in ball y r, G z = ∫⁻ z, ballInd G r (y, z) := by
    intro y
    rw [← lintegral_indicator measurableSet_ball]
    exact lintegral_congr (fun z => (ballInd_eq G r y z).symm)
  have hfun : (fun y => termR G r y)
      = fun y => (volume (ball (0 : Space) r))⁻¹ * ∫⁻ z, ballInd G r (y, z) := by
    funext y
    unfold termR
    rw [Measure.addHaar_ball_center volume y r, hint y]
  rw [hfun]
  exact (hF.lintegral_prod_right').const_mul _

lemma termR_empty (G : Space → ℝ≥0∞) (y : Space) {q : ℝ} (hq : q ≤ 0) :
    termR G q y = 0 := by
  unfold termR
  rw [ball_eq_empty.mpr hq]
  simp

lemma termR_step (G : Space → ℝ≥0∞) (y : Space) {r q : ℝ} (hr : 0 < r) (hrq : r ≤ q) :
    termR G r y * ENNReal.ofReal ((r / q) ^ 3) ≤ termR G q y := by
  have hq : 0 < q := lt_of_lt_of_le hr hrq
  have hVr0 : volume (ball y r) ≠ 0 := (measure_ball_pos volume y hr).ne'
  have hVrt : volume (ball y r) ≠ ⊤ := (measure_ball_lt_top).ne
  have hVq0 : volume (ball y q) ≠ 0 := (measure_ball_pos volume y hq).ne'
  have hVqt : volume (ball y q) ≠ ⊤ := (measure_ball_lt_top).ne
  have hK' : ENNReal.ofReal ((r / q) ^ 3) * volume (ball y q) = volume (ball y r) := by
    rw [EuclideanSpace.volume_ball_fin_three, EuclideanSpace.volume_ball_fin_three]
    have h1 : ENNReal.ofReal ((r / q) ^ 3) * ENNReal.ofReal q ^ 3 = ENNReal.ofReal r ^ 3 := by
      rw [← ENNReal.ofReal_pow hq.le, ← ENNReal.ofReal_pow hr.le,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    calc ENNReal.ofReal ((r / q) ^ 3) * (ENNReal.ofReal q ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3))
        = (ENNReal.ofReal ((r / q) ^ 3) * ENNReal.ofReal q ^ 3) * ENNReal.ofReal (Real.pi * 4 / 3) := by
          ring
      _ = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by rw [h1]
  have hKe : ENNReal.ofReal ((r / q) ^ 3) = volume (ball y r) * (volume (ball y q))⁻¹ := by
    calc ENNReal.ofReal ((r / q) ^ 3)
        = ENNReal.ofReal ((r / q) ^ 3) * (volume (ball y q) * (volume (ball y q))⁻¹) := by
          rw [ENNReal.mul_inv_cancel hVq0 hVqt, mul_one]
      _ = (ENNReal.ofReal ((r / q) ^ 3) * volume (ball y q)) * (volume (ball y q))⁻¹ := by ring
      _ = volume (ball y r) * (volume (ball y q))⁻¹ := by rw [hK']
  have hN : ∫⁻ z in ball y r, G z ≤ ∫⁻ z in ball y q, G z :=
    lintegral_mono_set (ball_subset_ball hrq)
  unfold termR
  rw [hKe]
  calc ((volume (ball y r))⁻¹ * ∫⁻ z in ball y r, G z) * (volume (ball y r) * (volume (ball y q))⁻¹)
      = ((volume (ball y r))⁻¹ * volume (ball y r)) * (∫⁻ z in ball y r, G z)
          * (volume (ball y q))⁻¹ := by ring
    _ = (∫⁻ z in ball y r, G z) * (volume (ball y q))⁻¹ := by
          rw [ENNReal.inv_mul_cancel hVr0 hVrt, one_mul]
    _ ≤ (∫⁻ z in ball y q, G z) * (volume (ball y q))⁻¹ := by gcongr
    _ = (volume (ball y q))⁻¹ * ∫⁻ z in ball y q, G z := mul_comm _ _

lemma termR_approx (G : Space → ℝ≥0∞) (y : Space) {r : ℝ} (hr : 0 < r) :
    termR G r y ≤ ⨆ q : ℚ, termR G (q : ℝ) y := by
  have hex : ∀ n : ℕ, ∃ q : ℚ, r < (q : ℝ) ∧ (q : ℝ) < r + 1 / ((n : ℝ) + 1) := fun n => by
    apply exists_rat_btwn
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose qn hqn1 hqn2 using hex
  have hqt : Tendsto (fun n : ℕ => (qn n : ℝ)) atTop (𝓝 r) := by
    have hup : Tendsto (fun n : ℕ => r + 1 / ((n : ℝ) + 1)) atTop (𝓝 r) := by
      simpa using (tendsto_const_nhds (x := r)).add tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => (hqn1 n).le) (fun n => (hqn2 n).le)
  have hK : Tendsto (fun n : ℕ => ENNReal.ofReal ((r / (qn n : ℝ)) ^ 3)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (r / (qn n : ℝ)) ^ 3) atTop (𝓝 ((r / r) ^ 3)) :=
      ((tendsto_const_nhds (x := r)).div hqt hr.ne').pow 3
    rw [div_self hr.ne', one_pow] at h1
    have h2 := ENNReal.tendsto_ofReal h1
    rwa [ENNReal.ofReal_one] at h2
  have hlim := ENNReal.Tendsto.const_mul (a := termR G r y) hK (Or.inl one_ne_zero)
  rw [mul_one] at hlim
  refine le_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  exact (termR_step G y hr (hqn1 n).le).trans (le_iSup (fun q : ℚ => termR G (q : ℝ) y) (qn n))

lemma hlMax_eq_rat (G : Space → ℝ≥0∞) (y : Space) :
    hlMax G y = ⨆ q : ℚ, termR G (q : ℝ) y := by
  apply le_antisymm
  · unfold hlMax
    refine iSup_le fun r => ?_
    exact termR_approx G y r.2
  · refine iSup_le fun q => ?_
    by_cases hq : 0 < (q : ℝ)
    · exact le_iSup_of_le (⟨(q : ℝ), hq⟩ : {r : ℝ // 0 < r}) le_rfl
    · rw [termR_empty G y (not_lt.mp hq)]
      exact zero_le

theorem hlMaxMeasurable : HLMaxMeasurable := by
  intro G hG
  have hfun : hlMax G = fun y => ⨆ q : ℚ, termR G (q : ℝ) y := funext (hlMax_eq_rat G)
  rw [hfun]
  exact Measurable.iSup (fun q : ℚ => termR_measurable G hG (q : ℝ))

end UnforcedLeray.Short.PartIIIb.Concrete
