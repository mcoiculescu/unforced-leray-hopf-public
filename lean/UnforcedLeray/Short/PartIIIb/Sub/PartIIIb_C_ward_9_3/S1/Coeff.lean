import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Coeff

/-! Relaxed cutoff-coefficient bounds (constants depend on `ν, R`). -/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma tccW_bounds (t x1 x2 x3 w a v L M W V : ℝ) (ht0 : 4 / 5 ≤ t) (ht1 : t ≤ 1)
    (hx1 : |x1| ≤ M) (hx2 : |x2| ≤ M) (hx3 : |x3| ≤ M) (hM : 1 ≤ M)
    (hw0 : 0 ≤ w) (hW0 : 0 ≤ W) (hw1 : w ≤ W) (ha0 : 0 ≤ a) (haL : a ≤ L⁻¹) (hL : 0 < L)
    (hv : |v| ≤ V) (hV0 : 0 ≤ V) :
    |t * x1 - w * (4 * t * x1 + 4 * t ^ 2 * x2)| ≤ 100 * M * (1 + W) ∧
    |4 * v * t * x1| ≤ 100 * M * V ∧
    |-(2 * t * x1 + 2 * t ^ 2 * x2) * a ^ 2 + w * a ^ 2 * (32 * t * x1 + 40 * t ^ 2 * x2 + 8 * t ^ 3 * x3)|
      ≤ 100 * M * (1 + W) * (L⁻¹) ^ 2 ∧
    |-2 * w * (6 * t * x1 + 4 * t ^ 2 * x2)| ≤ 100 * M * (1 + W) := by
  have ht0' : 0 ≤ t := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hLinv : 0 ≤ L⁻¹ := inv_nonneg.2 hL.le
  have hpt2 : |t ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg t)]
    nlinarith
  have hpt3 : |t ^ 3| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg ht0' 3)]
    have h2 : t ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hp1 : |t * x1| ≤ M := by
    rw [abs_mul, abs_of_nonneg ht0']
    have h := mul_le_mul_of_nonneg_right ht1 (abs_nonneg x1)
    linarith
  have hp2 : |t ^ 2 * x2| ≤ M := by
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_right hpt2 (abs_nonneg x2)
    linarith
  have hp3 : |t ^ 3 * x3| ≤ M := by
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_right hpt3 (abs_nonneg x3)
    linarith
  obtain ⟨hp1l, hp1u⟩ := abs_le.1 hp1
  obtain ⟨hp2l, hp2u⟩ := abs_le.1 hp2
  obtain ⟨hp3l, hp3u⟩ := abs_le.1 hp3
  have hX : |4 * t * x1 + 4 * t ^ 2 * x2| ≤ 8 * M := by
    rw [abs_le]; constructor <;> linarith
  have hY : |6 * t * x1 + 4 * t ^ 2 * x2| ≤ 10 * M := by
    rw [abs_le]; constructor <;> linarith
  have hQ : |2 * t * x1 + 2 * t ^ 2 * x2| ≤ 4 * M := by
    rw [abs_le]; constructor <;> linarith
  have hR3 : |32 * t * x1 + 40 * t ^ 2 * x2 + 8 * t ^ 3 * x3| ≤ 80 * M := by
    rw [abs_le]; constructor <;> linarith
  have hwX : |w * (4 * t * x1 + 4 * t ^ 2 * x2)| ≤ W * (8 * M) := by
    rw [abs_mul, abs_of_nonneg hw0]
    exact mul_le_mul hw1 hX (abs_nonneg _) hW0
  have hwY : |w * (6 * t * x1 + 4 * t ^ 2 * x2)| ≤ W * (10 * M) := by
    rw [abs_mul, abs_of_nonneg hw0]
    exact mul_le_mul hw1 hY (abs_nonneg _) hW0
  obtain ⟨hwXl, hwXu⟩ := abs_le.1 hwX
  obtain ⟨hwYl, hwYu⟩ := abs_le.1 hwY
  have ha2 : a ^ 2 ≤ (L⁻¹) ^ 2 := by
    have h := mul_le_mul haL haL ha0 hLinv
    linarith
  have ha2' : 0 ≤ a ^ 2 := sq_nonneg a
  have hML : 0 ≤ M * L⁻¹ := mul_nonneg hM0 hLinv
  have hML2 : 0 ≤ M * (L⁻¹) ^ 2 := mul_nonneg hM0 (sq_nonneg _)
  have hMW : 0 ≤ M * W := mul_nonneg hM0 hW0
  have hMV : 0 ≤ M * V := mul_nonneg hM0 hV0
  have hMWL2 : 0 ≤ M * W * (L⁻¹) ^ 2 := mul_nonneg hMW (sq_nonneg _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · have hv2 : |v| * |t * x1| ≤ V * M := mul_le_mul hv hp1 (abs_nonneg _) hV0
    have key : |4 * v * t * x1| = 4 * (|v| * |t * x1|) := by
      rw [show (4 : ℝ) * v * t * x1 = 4 * (v * (t * x1)) by ring, abs_mul, abs_mul]
      norm_num
    rw [key]
    linarith
  · have e1 : |(2 * t * x1 + 2 * t ^ 2 * x2) * a ^ 2| ≤ 4 * M * (L⁻¹) ^ 2 := by
      rw [abs_mul, abs_of_nonneg ha2']
      exact mul_le_mul hQ ha2 ha2' (by linarith)
    have hwa : w * a ^ 2 ≤ W * (L⁻¹) ^ 2 := mul_le_mul hw1 ha2 ha2' hW0
    have e2 : |w * a ^ 2 * (32 * t * x1 + 40 * t ^ 2 * x2 + 8 * t ^ 3 * x3)| ≤
        W * (L⁻¹) ^ 2 * (80 * M) := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hw0 ha2')]
      exact mul_le_mul hwa hR3 (abs_nonneg _) (by positivity)
    obtain ⟨e1l, e1u⟩ := abs_le.1 e1
    obtain ⟨e2l, e2u⟩ := abs_le.1 e2
    rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith


theorem tcCoeffW (χy : ℝ → ℝ) (hχ : IsStreamCutoff χy) : ∃ M : ℝ, 1 ≤ M ∧
    ∀ (ν R : ℝ), 0 < ν → 0 < R →
      ∀ r : ℝ, R * Real.sqrt ν ≤ r → r ≤ R * Real.sqrt (5 * ν / 4) →
        |tcA1 ν R χy r| ≤ 100 * M * (1 + ν * ((R * Real.sqrt ν)⁻¹) ^ 2) ∧
        |tcA2 ν R χy r| ≤ 100 * M * (ν * (R * Real.sqrt ν)⁻¹) ∧
        |tcB1 ν R χy r| ≤ 100 * M * (1 + ν * ((R * Real.sqrt ν)⁻¹) ^ 2) * ((R * Real.sqrt ν)⁻¹) ^ 2 ∧
        |tcB2 ν R χy r| ≤ 100 * M * (1 + ν * ((R * Real.sqrt ν)⁻¹) ^ 2) := by
  obtain ⟨d0, d1, d2, c1, c2, c3⟩ := tcc_smooth χy hχ
  obtain ⟨M1, hM1⟩ := tcc_bounded _ c1
  obtain ⟨M2, hM2⟩ := tcc_bounded _ c2
  obtain ⟨M3, hM3⟩ := tcc_bounded _ c3
  obtain ⟨M, hM, hMb⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ t ∈ Icc (4 / 5 : ℝ) 1,
      |deriv χy t| ≤ M ∧ |deriv (deriv χy) t| ≤ M ∧ |deriv (deriv (deriv χy)) t| ≤ M := by
    refine ⟨|M1| + |M2| + |M3| + 1, ?_, fun t ht => ⟨?_, ?_, ?_⟩⟩
    · have := abs_nonneg M1; have := abs_nonneg M2; have := abs_nonneg M3; linarith
    · have := hM1 t ht; have := le_abs_self M1; have := abs_nonneg M2; have := abs_nonneg M3
      linarith
    · have := hM2 t ht; have := le_abs_self M2; have := abs_nonneg M1; have := abs_nonneg M3
      linarith
    · have := hM3 t ht; have := le_abs_self M3; have := abs_nonneg M1; have := abs_nonneg M2
      linarith
  refine ⟨M, hM, ?_⟩
  intro ν R hν hR r hr1 hr2
  have hL : 0 < R * Real.sqrt ν := mul_pos hR (Real.sqrt_pos.2 hν)
  have hr : 0 < r := lt_of_lt_of_le hL hr1
  have hr0 : r ≠ 0 := hr.ne'
  have hsq1 : (R * Real.sqrt ν) ^ 2 = R ^ 2 * ν := by
    rw [mul_pow, Real.sq_sqrt hν.le]
  have hsq2 : (R * Real.sqrt (5 * ν / 4)) ^ 2 = R ^ 2 * (5 * ν / 4) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hLr2 : (R * Real.sqrt ν) ^ 2 ≤ r ^ 2 := by
    have h := mul_le_mul hr1 hr1 hL.le hr.le
    linarith [h, sq (R * Real.sqrt ν), sq r]
  have hr2' : r ^ 2 ≤ (R * Real.sqrt (5 * ν / 4)) ^ 2 := by
    have h := mul_le_mul hr2 hr2 hr.le (le_trans hr.le hr2)
    linarith [h, sq (R * Real.sqrt (5 * ν / 4)), sq r]
  have ht_def : ν * (R ^ 2 / r ^ 2) = (R ^ 2 * ν) / r ^ 2 := by ring
  have ht1 : ν * (R ^ 2 / r ^ 2) ≤ 1 := by
    rw [ht_def, div_le_one (by positivity)]
    linarith
  have ht0 : 4 / 5 ≤ ν * (R ^ 2 / r ^ 2) := by
    rw [ht_def, le_div_iff₀ (by positivity)]
    rw [hsq2] at hr2'
    linarith
  have hw0 : 0 ≤ ν * (r⁻¹) ^ 2 := by positivity
  have ha0 : 0 ≤ r⁻¹ := inv_nonneg.2 hr.le
  have haL : r⁻¹ ≤ (R * Real.sqrt ν)⁻¹ := inv_anti₀ hL hr1
  have hw1 : ν * (r⁻¹) ^ 2 ≤ ν * ((R * Real.sqrt ν)⁻¹) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0 haL 2) hν.le
  have hW0 : 0 ≤ ν * ((R * Real.sqrt ν)⁻¹) ^ 2 := by positivity
  have hV0 : 0 ≤ ν * (R * Real.sqrt ν)⁻¹ := by positivity
  have hv : |ν * r⁻¹| ≤ ν * (R * Real.sqrt ν)⁻¹ := by
    rw [abs_of_nonneg (mul_nonneg hν.le ha0)]
    exact mul_le_mul_of_nonneg_left haL hν.le
  have hm := hMb _ ⟨ht0, ht1⟩
  -- derivative identities
  have hdC0 := tcc_deriv_C0 χy d0 ν R r hr0
  have hdd := tcc_deriv_deriv_C0 χy d0 d1 ν R r hr
  have hF := tcc_tcF0_eq χy ν R r
  have hF1 := tcc_deriv_F0 χy d1 ν R r hr
  have hF2 := tcc_deriv_deriv_F0 χy d1 d2 ν R r hr
  have eA1 : tcA1 ν R χy r =
      (ν * (R ^ 2 / r ^ 2)) * deriv χy (ν * (R ^ 2 / r ^ 2)) -
        (ν * r⁻¹ ^ 2) * (4 * (ν * (R ^ 2 / r ^ 2)) * deriv χy (ν * (R ^ 2 / r ^ 2)) +
          4 * (ν * (R ^ 2 / r ^ 2)) ^ 2 * deriv (deriv χy) (ν * (R ^ 2 / r ^ 2))) := by
    unfold tcA1
    rw [hdC0, hdd]
    tcc_fsr
  have eA2 : tcA2 ν R χy r =
      4 * (ν * r⁻¹) * (ν * (R ^ 2 / r ^ 2)) * deriv χy (ν * (R ^ 2 / r ^ 2)) := by
    unfold tcA2
    rw [hdC0]
    tcc_fsr
  have eB1 : tcB1 ν R χy r =
      -(2 * (ν * (R ^ 2 / r ^ 2)) * deriv χy (ν * (R ^ 2 / r ^ 2)) +
          2 * (ν * (R ^ 2 / r ^ 2)) ^ 2 * deriv (deriv χy) (ν * (R ^ 2 / r ^ 2))) * (r⁻¹) ^ 2 +
        (ν * (r⁻¹) ^ 2) * (r⁻¹) ^ 2 *
          (32 * (ν * (R ^ 2 / r ^ 2)) * deriv χy (ν * (R ^ 2 / r ^ 2)) +
            40 * (ν * (R ^ 2 / r ^ 2)) ^ 2 * deriv (deriv χy) (ν * (R ^ 2 / r ^ 2)) +
            8 * (ν * (R ^ 2 / r ^ 2)) ^ 3 * deriv (deriv (deriv χy)) (ν * (R ^ 2 / r ^ 2))) := by
    unfold tcB1
    rw [hF, hF1, hF2]
    tcc_fsr
  have eB2 : tcB2 ν R χy r =
      -2 * (ν * (r⁻¹) ^ 2) *
        (6 * (ν * (R ^ 2 / r ^ 2)) * deriv χy (ν * (R ^ 2 / r ^ 2)) +
          4 * (ν * (R ^ 2 / r ^ 2)) ^ 2 * deriv (deriv χy) (ν * (R ^ 2 / r ^ 2))) := by
    unfold tcB2
    rw [hF, hF1]
    tcc_fsr
  obtain ⟨b1, b2, b3, b4⟩ := tccW_bounds (ν * (R ^ 2 / r ^ 2))
    (deriv χy (ν * (R ^ 2 / r ^ 2))) (deriv (deriv χy) (ν * (R ^ 2 / r ^ 2)))
    (deriv (deriv (deriv χy)) (ν * (R ^ 2 / r ^ 2))) (ν * (r⁻¹) ^ 2) r⁻¹ (ν * r⁻¹)
    (R * Real.sqrt ν) M (ν * ((R * Real.sqrt ν)⁻¹) ^ 2) (ν * (R * Real.sqrt ν)⁻¹) ht0 ht1 hm.1 hm.2.1 hm.2.2 hM hw0 hW0 hw1 ha0 haL hL hv hV0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eA1]
    exact b1
  · rw [eA2]
    exact b2
  · rw [eB1]
    exact b3
  · rw [eB2]
    exact b4


end UnforcedLeray.Short.PartIIIb.Concrete

end
