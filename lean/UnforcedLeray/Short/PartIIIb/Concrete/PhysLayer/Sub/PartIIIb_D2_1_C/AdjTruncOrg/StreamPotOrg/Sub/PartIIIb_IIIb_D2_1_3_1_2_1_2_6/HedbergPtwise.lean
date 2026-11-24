import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.HedbergNear
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.HedbergFar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.OuterMeasure.AE

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Real power identity `(x ^ a) ^ 2 = x ^ (2 a)` for `x ≥ 0`. -/
lemma sq_rpow_aux (x : ℝ) (hx : 0 ≤ x) (a : ℝ) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- Real optimisation of the two-term Hedberg bound with `R = q / p²`, `p = m^{1/3}`, `q = b^{1/3}`. -/
lemma real_hedberg_aux (m b : ℝ) (hm : 0 < m) (hb : 0 < b) :
    ∃ R : ℝ, 0 < R ∧
      R * m + b ^ (1 / 2 : ℝ) * (4 * Real.pi * R) ^ (-(1 / 2 : ℝ))
        ≤ 2 * m ^ (1 / 3 : ℝ) * b ^ (1 / 3 : ℝ) := by
  obtain ⟨p, hp_def⟩ : ∃ p : ℝ, p = m ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = b ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  rw [← hp_def, ← hq_def]
  have hp : 0 < p := by rw [hp_def]; exact Real.rpow_pos_of_pos hm _
  have hq : 0 < q := by rw [hq_def]; exact Real.rpow_pos_of_pos hb _
  have hp0 : p ≠ 0 := hp.ne'
  have hq0 : q ≠ 0 := hq.ne'
  have hpi0 : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hp3 : p ^ 3 = m := by
    rw [hp_def, ← Real.rpow_natCast, ← Real.rpow_mul hm.le]
    norm_num
  have hq3 : q ^ 3 = b := by
    rw [hq_def, ← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    norm_num
  have hR : 0 < q / p ^ 2 := div_pos hq (pow_pos hp 2)
  refine ⟨q / p ^ 2, hR, ?_⟩
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = b ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨v, hv_def⟩ : ∃ v : ℝ, v = (4 * Real.pi * (q / p ^ 2)) ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  rw [← hu_def, ← hv_def]
  have hu0 : 0 ≤ u := by rw [hu_def]; exact Real.rpow_nonneg hb.le _
  have hv0 : 0 ≤ v := by
    rw [hv_def]
    exact Real.rpow_nonneg (mul_nonneg (by positivity) hR.le) _
  have hu2 : u ^ 2 = b := by
    rw [hu_def, sq_rpow_aux b hb.le]
    norm_num
  have hv2 : v ^ 2 = (4 * Real.pi * (q / p ^ 2))⁻¹ := by
    rw [hv_def, sq_rpow_aux _ (mul_nonneg (by positivity) hR.le),
      show (2 : ℝ) * (-(1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
  have hdiv : (4 * Real.pi * (q / p ^ 2))⁻¹ * b = q ^ 2 * p ^ 2 / (4 * Real.pi) := by
    rw [← hq3]
    field_simp
  have hle : q ^ 2 * p ^ 2 / (4 * Real.pi) ≤ (p * q) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three, mul_nonneg (sq_nonneg (p * q))
      (by linarith [Real.pi_gt_three] : (0 : ℝ) ≤ 4 * Real.pi - 1)]
  have hsq : (u * v) ^ 2 ≤ (p * q) ^ 2 := by
    have e : (u * v) ^ 2 = (4 * Real.pi * (q / p ^ 2))⁻¹ * b := by
      rw [mul_pow, hu2, hv2]
      ring
    rw [e, hdiv]
    exact hle
  have huv : u * v ≤ p * q := by
    nlinarith [mul_nonneg hu0 hv0, mul_pos hp hq, hsq]
  have hRm : q / p ^ 2 * m = p * q := by
    rw [← hp3]
    field_simp
  linarith [hRm, huv]

/-- Scalar ENNReal core of Hedberg's bound in the finite, nonzero case. -/
lemma hedberg_ennreal_main (M B T : ℝ≥0∞)
    (hsplit : ∀ R : ℝ, 0 < R →
      T ≤ ENNReal.ofReal R * M + B ^ (1 / 2 : ℝ) * ENNReal.ofReal ((4 * Real.pi * R) ^ (-(1 / 2 : ℝ))))
    (hM0 : M ≠ 0) (hMt : M ≠ ⊤) (hB0 : B ≠ 0) (hBt : B ≠ ⊤) :
    T ≤ 2 * M ^ (1 / 3 : ℝ) * B ^ (1 / 3 : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℝ, M = ENNReal.ofReal m :=
    ⟨M.toReal, (ENNReal.ofReal_toReal hMt).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℝ, B = ENNReal.ofReal b :=
    ⟨B.toReal, (ENNReal.ofReal_toReal hBt).symm⟩
  have hm : 0 < m := by
    rcases lt_or_ge 0 m with h | h
    · exact h
    · exact absurd (ENNReal.ofReal_eq_zero.2 h) hM0
  have hb : 0 < b := by
    rcases lt_or_ge 0 b with h | h
    · exact h
    · exact absurd (ENNReal.ofReal_eq_zero.2 h) hB0
  obtain ⟨R, hR, hbound⟩ := real_hedberg_aux m b hm hb
  have h1 := hsplit R hR
  rw [ENNReal.ofReal_rpow_of_nonneg hb.le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h1
  have hpos1 : 0 ≤ R * m := mul_nonneg hR.le hm.le
  have hpos2 : 0 ≤ b ^ (1 / 2 : ℝ) * (4 * Real.pi * R) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hb.le _)
      (Real.rpow_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hR.le) _)
  rw [← ENNReal.ofReal_mul hR.le, ← ENNReal.ofReal_mul (Real.rpow_nonneg hb.le _),
    ← ENNReal.ofReal_add hpos1 hpos2] at h1
  have h2m : 0 ≤ 2 * m ^ (1 / 3 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hm.le _)
  calc T ≤ ENNReal.ofReal (R * m + b ^ (1 / 2 : ℝ) * (4 * Real.pi * R) ^ (-(1 / 2 : ℝ))) := h1
    _ ≤ ENNReal.ofReal (2 * m ^ (1 / 3 : ℝ) * b ^ (1 / 3 : ℝ)) := ENNReal.ofReal_le_ofReal hbound
    _ = 2 * ENNReal.ofReal m ^ (1 / 3 : ℝ) * ENNReal.ofReal b ^ (1 / 3 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hm.le (by norm_num : (0 : ℝ) ≤ 1 / 3),
        ENNReal.ofReal_rpow_of_nonneg hb.le (by norm_num : (0 : ℝ) ≤ 1 / 3),
        ENNReal.ofReal_mul h2m, ENNReal.ofReal_mul (p := 2) (by norm_num),
        ENNReal.ofReal_ofNat]

/-- If `hlMax G y = 0` then `G = 0` a.e. -/
lemma ae_zero_of_hlMax_zero {G : Space → ℝ≥0∞} (hG : Measurable G) {y : Space}
    (h : hlMax G y = 0) : ∀ᵐ z ∂(volume : Measure Space), G z = 0 := by
  have hball : ∀ n : ℕ, ∫⁻ z in ball y ((n : ℝ) + 1), G z = 0 := by
    intro n
    have hr : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle : (volume (ball y ((n : ℝ) + 1)))⁻¹ * ∫⁻ z in ball y ((n : ℝ) + 1), G z
        ≤ hlMax G y :=
      le_iSup (fun r : {r : ℝ // 0 < r} => (volume (ball y r.1))⁻¹ * ∫⁻ z in ball y r.1, G z)
        ⟨(n : ℝ) + 1, hr⟩
    rw [h] at hle
    have hpos : (volume (ball y ((n : ℝ) + 1)))⁻¹ ≠ 0 :=
      ENNReal.inv_ne_zero.2 measure_ball_lt_top.ne
    have h0 : (volume (ball y ((n : ℝ) + 1)))⁻¹ * ∫⁻ z in ball y ((n : ℝ) + 1), G z = 0 :=
      le_antisymm hle zero_le
    exact (mul_eq_zero.1 h0).resolve_left hpos
  have hae : ∀ n : ℕ, ∀ᵐ z ∂(volume : Measure Space), z ∈ ball y ((n : ℝ) + 1) → G z = 0 := by
    intro n
    have h1 := (lintegral_eq_zero_iff hG).1 (hball n)
    exact ae_imp_of_ae_restrict h1
  filter_upwards [ae_all_iff.2 hae] with z hz
  obtain ⟨n, hn⟩ := exists_nat_gt (dist z y)
  exact hz n (by rw [Metric.mem_ball]; linarith)

/-- If `G = 0` a.e. then the Biot-Savart potential vanishes. -/
lemma rieszT_eq_zero_of_ae {G : Space → ℝ≥0∞} {y : Space}
    (h : ∀ᵐ z ∂(volume : Measure Space), G z = 0) : rieszT G y = 0 := by
  unfold rieszT
  have hfg : (fun z => G z * bsK2 (y - z)) =ᵐ[volume] (fun _ => (0 : ℝ≥0∞)) := by
    filter_upwards [h] with z hz
    simp [hz]
  rw [lintegral_congr_ae hfg, lintegral_zero]

theorem hedbergPtwise : HedbergPtwise := by
  intro G hG y
  have hsplit : ∀ R : ℝ, 0 < R → rieszT G y ≤
      ENNReal.ofReal R * hlMax G y
        + (∫⁻ z, (G z) ^ 2) ^ (1 / 2 : ℝ) * ENNReal.ofReal ((4 * Real.pi * R) ^ (-(1 / 2 : ℝ))) := by
    intro R hR
    unfold rieszT
    calc ∫⁻ z, G z * bsK2 (y - z)
        = (∫⁻ z in ball y R, G z * bsK2 (y - z)) + (∫⁻ z in (ball y R)ᶜ, G z * bsK2 (y - z)) :=
          (lintegral_add_compl _ measurableSet_ball).symm
      _ ≤ _ := add_le_add (hedbergNear G hG y R hR) (hedbergFar G hG y R hR)
  by_cases hM0 : hlMax G y = 0
  · rw [rieszT_eq_zero_of_ae (ae_zero_of_hlMax_zero hG hM0)]
    exact zero_le
  by_cases hB0 : (∫⁻ z, (G z) ^ 2) = 0
  · have hae : ∀ᵐ z ∂(volume : Measure Space), G z = 0 := by
      have h2 := (lintegral_eq_zero_iff (hG.pow_const 2)).1 hB0
      filter_upwards [h2] with z hz
      simpa using hz
    rw [rieszT_eq_zero_of_ae hae]
    exact zero_le
  by_cases hMt : hlMax G y = ⊤
  · have hX : 0 < (∫⁻ z, (G z) ^ 2) ^ (1 / 3 : ℝ) :=
      ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hB0) (by norm_num)
    have hR : 2 * (hlMax G y) ^ (1 / 3 : ℝ) * (∫⁻ z, (G z) ^ 2) ^ (1 / 3 : ℝ) = ⊤ := by
      rw [hMt, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 3),
        ENNReal.mul_top two_ne_zero, ENNReal.top_mul hX.ne']
    rw [hR]
    exact le_top
  by_cases hBt : (∫⁻ z, (G z) ^ 2) = ⊤
  · have hX : 0 < (hlMax G y) ^ (1 / 3 : ℝ) :=
      ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hM0) (by norm_num)
    have hR : 2 * (hlMax G y) ^ (1 / 3 : ℝ) * (∫⁻ z, (G z) ^ 2) ^ (1 / 3 : ℝ) = ⊤ := by
      rw [hBt, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 3),
        ENNReal.mul_top (mul_ne_zero two_ne_zero hX.ne')]
    rw [hR]
    exact le_top
  exact hedberg_ennreal_main (hlMax G y) (∫⁻ z, (G z) ^ 2) (rieszT G y) hsplit hM0 hMt hB0 hBt

end UnforcedLeray.Short.PartIIIb.Concrete
