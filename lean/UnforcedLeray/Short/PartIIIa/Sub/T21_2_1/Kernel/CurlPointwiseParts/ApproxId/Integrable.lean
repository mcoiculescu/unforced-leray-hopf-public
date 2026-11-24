import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_6_2
import UnforcedLeray.Units.B0579
import UnforcedLeray.Units.B0592.Kernel

/-!
# `KerLapInt`: integrability of the regularised Laplacian on the cell (SP 2081-2084)

`lapForm d ε z = (π ε/d²)(cosh φ + cos θ)/(cosh φ - cos θ + ε)²`, with `φ = 2πη/d`, `θ = 2πq/d`.
Since `cosh φ - cos θ + ε ≥ min(ε,1) cosh φ` and `cosh φ ≥ κ(1+η²)` (from `sinh` lower bounds),
`lapForm ≤ K (1+η²)⁻¹`, which is integrable on the cell (a product of an indicator in `q` and an
integrable function of `η`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

lemma kLI_cosh_lower {d : ℝ} (hd : 0 < d) (η : ℝ) :
    1 + 8 * η ^ 2 / d ^ 2 ≤ Real.cosh (2 * Real.pi * η / d) := by
  have h2 : 2 * Real.pi * η / d = 2 * (Real.pi * η / d) := by ring
  rw [h2, Real.cosh_two_mul]
  have hc := Real.cosh_sq (Real.pi * η / d)
  have hs := UnforcedLeray.B0592.sinh_sq_lower hd η
  have h8 : 8 * η ^ 2 / d ^ 2 ≤ 2 * Real.sinh (Real.pi * η / d) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hs]
  nlinarith [hc, h8]

/-- Pure real inequality behind the pointwise bound. -/
lemma kLI_alg (A ε m κ C c η : ℝ) (hA : 0 ≤ A) (hm : 0 < m) (hmε : m ≤ ε) (hm1 : m ≤ 1)
    (hκ : 0 < κ) (hC : κ * (1 + η ^ 2) ≤ C) (hC1 : 1 ≤ C) (hc1 : c ≤ 1) :
    A * (C + c) / (C - c + ε) ^ 2 ≤ 2 * A / m ^ 2 / κ * (1 + η ^ 2)⁻¹ := by
  have hD : m * C ≤ C - c + ε := by
    nlinarith [mul_nonneg (sub_nonneg.2 hC1) (sub_nonneg.2 hm1)]
  have hCpos : 0 < C := by linarith
  have hmC : 0 < m * C := mul_pos hm hCpos
  have hD2 : (m * C) ^ 2 ≤ (C - c + ε) ^ 2 := pow_le_pow_left₀ hmC.le hD 2
  have hnum : A * (C + c) ≤ A * (2 * C) := mul_le_mul_of_nonneg_left (by linarith) hA
  have s1 : A * (C + c) / (C - c + ε) ^ 2 ≤ A * (2 * C) / (C - c + ε) ^ 2 :=
    div_le_div_of_nonneg_right hnum (sq_nonneg _)
  have s2 : A * (2 * C) / (C - c + ε) ^ 2 ≤ A * (2 * C) / (m * C) ^ 2 :=
    div_le_div_of_nonneg_left (mul_nonneg hA (by linarith)) (pow_pos hmC 2) hD2
  have s3 : A * (2 * C) / (m * C) ^ 2 = 2 * A / m ^ 2 * (1 / C) := by
    field_simp
  have hpos : 0 < κ * (1 + η ^ 2) := mul_pos hκ (by positivity)
  have hinv : 1 / C ≤ κ⁻¹ * (1 + η ^ 2)⁻¹ := by
    calc 1 / C ≤ 1 / (κ * (1 + η ^ 2)) := one_div_le_one_div_of_le hpos hC
      _ = κ⁻¹ * (1 + η ^ 2)⁻¹ := by rw [one_div, mul_inv]
  have hK0 : 0 ≤ 2 * A / m ^ 2 := div_nonneg (by linarith) (by positivity)
  have s4 : 2 * A / m ^ 2 * (1 / C) ≤ 2 * A / m ^ 2 * (κ⁻¹ * (1 + η ^ 2)⁻¹) :=
    mul_le_mul_of_nonneg_left hinv hK0
  have s5 : 2 * A / m ^ 2 * (κ⁻¹ * (1 + η ^ 2)⁻¹) = 2 * A / m ^ 2 / κ * (1 + η ^ 2)⁻¹ := by
    ring
  linarith [s1, s2, s3, s4, s5]

/-- Pointwise domination `lapForm ≤ K (1+η²)⁻¹`, uniformly in `q`. -/
lemma kLI_bound (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ z : ℝ × ℝ, lapForm d ε z ≤ K * (1 + z.2 ^ 2)⁻¹ := by
  have hm : 0 < min ε 1 := lt_min hε one_pos
  have hκ : 0 < min 1 (8 / d ^ 2) := lt_min one_pos (by positivity)
  have hκ1 : min 1 (8 / d ^ 2) ≤ 1 := min_le_left _ _
  have hκ2 : min 1 (8 / d ^ 2) ≤ 8 / d ^ 2 := min_le_right _ _
  have hA : 0 ≤ Real.pi * ε / d ^ 2 := div_nonneg (mul_nonneg Real.pi_pos.le hε.le) (sq_nonneg d)
  refine ⟨2 * (Real.pi * ε / d ^ 2) / (min ε 1) ^ 2 / (min 1 (8 / d ^ 2)), fun z => ?_⟩
  have hcosh := kLI_cosh_lower hd z.2
  have hκC : min 1 (8 / d ^ 2) * (1 + z.2 ^ 2) ≤ Real.cosh (2 * Real.pi * z.2 / d) := by
    have h1 : min 1 (8 / d ^ 2) * z.2 ^ 2 ≤ 8 / d ^ 2 * z.2 ^ 2 :=
      mul_le_mul_of_nonneg_right hκ2 (sq_nonneg _)
    have e : 8 / d ^ 2 * z.2 ^ 2 = 8 * z.2 ^ 2 / d ^ 2 := by ring
    nlinarith [h1, e, hcosh]
  unfold lapForm UnforcedLeray.B0592.den
  exact kLI_alg (Real.pi * ε / d ^ 2) ε (min ε 1) (min 1 (8 / d ^ 2))
    (Real.cosh (2 * Real.pi * z.2 / d)) (Real.cos (2 * Real.pi * z.1 / d)) z.2 hA hm
    (min_le_left _ _) (min_le_right _ _) hκ hκC
    (Real.one_le_cosh _) (Real.cos_le_one _)

theorem kerLapInt : UnforcedLeray.Short.IIIa.KerLapInt := by
  intro d ε hd hε
  obtain ⟨K, hK⟩ := kLI_bound d ε hd hε
  have hg1 : Integrable (fun q : ℝ => (Set.Ico (-(d / 2)) (d / 2)).indicator (fun _ => (1 : ℝ)) q) := by
    refine (integrable_indicator_iff measurableSet_Ico).2 ?_
    exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have hg2 : Integrable (fun η : ℝ => K * (1 + η ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hprod : Integrable (fun z : ℝ × ℝ =>
      (Set.Ico (-(d / 2)) (d / 2)).indicator (fun _ => (1 : ℝ)) z.1 * (K * (1 + z.2 ^ 2)⁻¹)) := by
    rw [Measure.volume_eq_prod]
    exact hg1.mul_prod hg2
  have hmeas : Measurable (lapForm d ε) := by
    unfold lapForm UnforcedLeray.B0592.den
    fun_prop
  refine Integrable.mono' hprod.integrableOn hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (B0579.measurableSet_cell d)] with z hz
  have hzI : z.1 ∈ Set.Ico (-(d / 2)) (d / 2) := hz.1
  rw [Real.norm_of_nonneg (lapForm_nonneg d ε hd hε z)]
  simp only [Set.indicator_of_mem hzI, one_mul]
  exact hK z

end UnforcedLeray.Short.IIIa
