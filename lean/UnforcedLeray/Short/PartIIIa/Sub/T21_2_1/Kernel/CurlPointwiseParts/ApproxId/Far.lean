import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_6_2
import UnforcedLeray.Units.B0579
import UnforcedLeray.Units.B0592.Kernel

/-!
# `KerLapFar`: the far tail of the regularised Laplacian (SP 2081-2084)

On the cell with `‖z‖ ≥ δ` one has `den d z ≥ 8δ²/d²` (`sin_sq_lower`, `sinh_sq_lower`,
`norm_sq_le`), hence `den ≥ lm cosh` with `lm = min(1/2, 4δ²/d²)`, and
`lapForm = (π/d²) ε (cosh + cos)/(den + ε)² ≤ ε K₁ (1+η²)⁻¹` uniformly in `ε ≤ 1`.
Integrating the dominator over the cell gives the constant `C = K₁ ∫_cell (1+η²)⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

def kFar_lam (d δ : ℝ) : ℝ := min (1 / 2 : ℝ) (8 * δ ^ 2 / d ^ 2 / 2)

def kFar_k0 (d : ℝ) : ℝ := min 1 (8 / d ^ 2)

def kFar_K1 (d δ : ℝ) : ℝ :=
  Real.pi / d ^ 2 * 2 / (kFar_lam d δ ^ 2 * kFar_k0 d)

lemma kFar_cosh_lower {d : ℝ} (hd : 0 < d) (η : ℝ) :
    1 + 8 * η ^ 2 / d ^ 2 ≤ Real.cosh (2 * Real.pi * η / d) := by
  have h2 : 2 * Real.pi * η / d = 2 * (Real.pi * η / d) := by ring
  rw [h2, Real.cosh_two_mul]
  have hc := Real.cosh_sq (Real.pi * η / d)
  have hs := UnforcedLeray.B0592.sinh_sq_lower hd η
  have h8 : 8 * η ^ 2 / d ^ 2 ≤ 2 * Real.sinh (Real.pi * η / d) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hs]
  nlinarith [hc, h8]

lemma kFar_cosh_kappa {d : ℝ} (hd : 0 < d) (η : ℝ) :
    kFar_k0 d * (1 + η ^ 2) ≤ Real.cosh (2 * Real.pi * η / d) := by
  have hκ2 : kFar_k0 d ≤ 8 / d ^ 2 := min_le_right _ _
  have h1 : kFar_k0 d * η ^ 2 ≤ 8 / d ^ 2 * η ^ 2 :=
    mul_le_mul_of_nonneg_right hκ2 (sq_nonneg _)
  have e : 8 / d ^ 2 * η ^ 2 = 8 * η ^ 2 / d ^ 2 := by ring
  have hκ1 : kFar_k0 d ≤ 1 := min_le_left _ _
  nlinarith [h1, e, kFar_cosh_lower hd η]

lemma kFar_k0_pos {d : ℝ} (hd : 0 < d) : 0 < kFar_k0 d :=
  lt_min one_pos (by positivity)

lemma kFar_lam_pos {d δ : ℝ} (hd : 0 < d) (hδ : 0 < δ) : 0 < kFar_lam d δ :=
  lt_min (by norm_num) (by positivity)

/-- On the cell with `‖z‖ ≥ δ`, `den ≥ 8δ²/d²`. -/
lemma kFar_den {d δ : ℝ} (hd : 0 < d) (hδ : 0 < δ) (z : ℝ × ℝ)
    (hz : z ∈ B0579.cell d) (hn : δ ≤ ‖z‖) :
    8 * δ ^ 2 / d ^ 2 ≤ UnforcedLeray.B0592.den d z := by
  have hq : |z.1| ≤ d / 2 := abs_le.2 ⟨hz.1.1, hz.1.2.le⟩
  have h1 := UnforcedLeray.B0592.sin_sq_lower hd hq
  have h2 := UnforcedLeray.B0592.sinh_sq_lower hd z.2
  have hden := UnforcedLeray.B0592.den_eq d z
  have hnorm : δ ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 :=
    le_trans (pow_le_pow_left₀ hδ.le hn 2) (UnforcedLeray.B0592.norm_sq_le z)
  rw [hden, div_le_iff₀ (by positivity)]
  nlinarith [h1, h2, hnorm]

/-- Pure real inequality behind the pointwise tail bound. -/
lemma kFar_alg (A ε C c η lm κ0 : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) (hlm : 0 < lm) (hκ0 : 0 < κ0)
    (hC1 : 1 ≤ C) (hc1 : c ≤ 1) (hden : lm * C ≤ C - c) (hCκ : κ0 * (1 + η ^ 2) ≤ C) :
    A * ε * (C + c) / (C - c + ε) ^ 2 ≤ ε * (A * 2 / (lm ^ 2 * κ0)) * (1 + η ^ 2)⁻¹ := by
  have hCpos : 0 < C := by linarith
  have hlmC : 0 < lm * C := mul_pos hlm hCpos
  have h1 : (lm * C) ^ 2 ≤ (C - c + ε) ^ 2 :=
    pow_le_pow_left₀ hlmC.le (by linarith) 2
  have hnum : A * ε * (C + c) ≤ A * ε * (2 * C) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA hε.le)
  have s1 : A * ε * (C + c) / (C - c + ε) ^ 2 ≤ A * ε * (2 * C) / (C - c + ε) ^ 2 :=
    div_le_div_of_nonneg_right hnum (sq_nonneg _)
  have s2 : A * ε * (2 * C) / (C - c + ε) ^ 2 ≤ A * ε * (2 * C) / (lm * C) ^ 2 :=
    div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hA hε.le) (by linarith)) (pow_pos hlmC 2) h1
  have s3 : A * ε * (2 * C) / (lm * C) ^ 2 = A * ε * 2 / lm ^ 2 * (1 / C) := by
    field_simp <;> ring
  have hpos : 0 < κ0 * (1 + η ^ 2) := mul_pos hκ0 (by positivity)
  have hinv : 1 / C ≤ κ0⁻¹ * (1 + η ^ 2)⁻¹ := by
    calc 1 / C ≤ 1 / (κ0 * (1 + η ^ 2)) := one_div_le_one_div_of_le hpos hCκ
      _ = κ0⁻¹ * (1 + η ^ 2)⁻¹ := by rw [one_div, mul_inv]
  have hK0 : 0 ≤ A * ε * 2 / lm ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hA hε.le) (by norm_num)) (sq_nonneg _)
  have s4 : A * ε * 2 / lm ^ 2 * (1 / C) ≤ A * ε * 2 / lm ^ 2 * (κ0⁻¹ * (1 + η ^ 2)⁻¹) :=
    mul_le_mul_of_nonneg_left hinv hK0
  have s5 : A * ε * 2 / lm ^ 2 * (κ0⁻¹ * (1 + η ^ 2)⁻¹) =
      ε * (A * 2 / (lm ^ 2 * κ0)) * (1 + η ^ 2)⁻¹ := by
    field_simp <;> ring
  linarith [s1, s2, s3, s4, s5]

/-- Pointwise tail bound, uniform in `ε > 0`. -/
lemma kFar_pt {d δ ε : ℝ} (hd : 0 < d) (hδ : 0 < δ) (hε : 0 < ε) (z : ℝ × ℝ)
    (hz : z ∈ B0579.cell d) (hn : δ ≤ ‖z‖) :
    UnforcedLeray.Short.IIIa.lapForm d ε z ≤ ε * kFar_K1 d δ * (1 + z.2 ^ 2)⁻¹ := by
  have hden := kFar_den hd hδ z hz hn
  have hden' : 8 * δ ^ 2 / d ^ 2 ≤ Real.cosh (2 * Real.pi * z.2 / d) -
      Real.cos (2 * Real.pi * z.1 / d) := hden
  have hκpos : 0 < 8 * δ ^ 2 / d ^ 2 := by positivity
  have hC1 : 1 ≤ Real.cosh (2 * Real.pi * z.2 / d) := Real.one_le_cosh _
  have hc1 : Real.cos (2 * Real.pi * z.1 / d) ≤ 1 := Real.cos_le_one _
  have hl1 : kFar_lam d δ ≤ 1 / 2 := min_le_left _ _
  have hl2 : kFar_lam d δ ≤ 8 * δ ^ 2 / d ^ 2 / 2 := min_le_right _ _
  have hdenlm : kFar_lam d δ * Real.cosh (2 * Real.pi * z.2 / d) ≤
      Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d) := by
    rcases le_total (Real.cosh (2 * Real.pi * z.2 / d)) 2 with h2 | h2
    · nlinarith [mul_le_mul_of_nonneg_right hl2 (by linarith : (0:ℝ) ≤ Real.cosh (2 * Real.pi * z.2 / d))]
    · nlinarith [mul_le_mul_of_nonneg_right hl1 (by linarith : (0:ℝ) ≤ Real.cosh (2 * Real.pi * z.2 / d))]
  have heq : UnforcedLeray.Short.IIIa.lapForm d ε z =
      Real.pi / d ^ 2 * ε * (Real.cosh (2 * Real.pi * z.2 / d) + Real.cos (2 * Real.pi * z.1 / d)) /
        (Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d) + ε) ^ 2 := by
    unfold UnforcedLeray.Short.IIIa.lapForm UnforcedLeray.B0592.den
    ring
  rw [heq]
  have hA : 0 ≤ Real.pi / d ^ 2 := div_nonneg Real.pi_pos.le (sq_nonneg d)
  have key := kFar_alg (Real.pi / d ^ 2) ε (Real.cosh (2 * Real.pi * z.2 / d))
    (Real.cos (2 * Real.pi * z.1 / d)) z.2 (kFar_lam d δ) (kFar_k0 d) hA hε
    (kFar_lam_pos hd hδ) (kFar_k0_pos hd) hC1 hc1 hdenlm (kFar_cosh_kappa hd z.2)
  unfold kFar_K1
  exact key

lemma kFar_K1_nonneg {d δ : ℝ} (hd : 0 < d) (hδ : 0 < δ) : 0 ≤ kFar_K1 d δ := by
  unfold kFar_K1
  exact div_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (kFar_k0_pos hd).le)

lemma kFar_h_int {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun x : ℝ × ℝ => (1 + x.2 ^ 2)⁻¹) (B0579.cell d) := by
  have hg1 : Integrable (fun q : ℝ => (Set.Ico (-(d / 2)) (d / 2)).indicator (fun _ => (1 : ℝ)) q) := by
    refine (integrable_indicator_iff measurableSet_Ico).2 ?_
    exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have hprod : Integrable (fun z : ℝ × ℝ =>
      (Set.Ico (-(d / 2)) (d / 2)).indicator (fun _ => (1 : ℝ)) z.1 * (1 + z.2 ^ 2)⁻¹)
      (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact hg1.mul_prod integrable_inv_one_add_sq
  refine Integrable.mono' hprod.integrableOn ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ × ℝ => (1 + x.2 ^ 2)⁻¹).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (B0579.measurableSet_cell d)] with z hz
    have hzI : z.1 ∈ Set.Ico (-(d / 2)) (d / 2) := hz.1
    simp only [Real.norm_eq_abs, Set.indicator_of_mem hzI, one_mul]
    rw [abs_of_nonneg (by positivity)]

theorem kerLapFar : UnforcedLeray.Short.IIIa.KerLapFar := by
  intro d δ hd hδ
  refine ⟨kFar_K1 d δ * ∫ x in B0579.cell d, (1 + x.2 ^ 2)⁻¹, fun ε hε hε1 => ?_⟩
  have hSm : MeasurableSet (B0579.cell d ∩ {x : ℝ × ℝ | δ ≤ ‖x‖}) :=
    (B0579.measurableSet_cell d).inter (isClosed_le continuous_const continuous_norm).measurableSet
  have hint : IntegrableOn (fun x : ℝ × ℝ => (1 + x.2 ^ 2)⁻¹) (B0579.cell d) := kFar_h_int hd
  have hintS : IntegrableOn (fun x : ℝ × ℝ => ε * kFar_K1 d δ * (1 + x.2 ^ 2)⁻¹)
      (B0579.cell d ∩ {x : ℝ × ℝ | δ ≤ ‖x‖}) :=
    ((hint.mono_set inter_subset_left).const_mul (ε * kFar_K1 d δ))
  have hlapS : IntegrableOn (UnforcedLeray.Short.IIIa.lapForm d ε)
      (B0579.cell d ∩ {x : ℝ × ℝ | δ ≤ ‖x‖}) := by
    refine Integrable.mono' hintS ?_ ?_
    · have hmeas : Measurable (UnforcedLeray.Short.IIIa.lapForm d ε) := by
        unfold UnforcedLeray.Short.IIIa.lapForm UnforcedLeray.B0592.den
        fun_prop
      exact hmeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hSm] with x hx
      rw [Real.norm_of_nonneg (UnforcedLeray.Short.IIIa.lapForm_nonneg d ε hd hε x)]
      exact kFar_pt hd hδ hε x hx.1 hx.2
  have step1 : ∫ x in B0579.cell d ∩ {x : ℝ × ℝ | δ ≤ ‖x‖},
      UnforcedLeray.Short.IIIa.lapForm d ε x ≤
      ∫ x in B0579.cell d ∩ {x : ℝ × ℝ | δ ≤ ‖x‖}, ε * kFar_K1 d δ * (1 + x.2 ^ 2)⁻¹ :=
    setIntegral_mono_on hlapS hintS hSm (fun x hx => kFar_pt hd hδ hε x hx.1 hx.2)
  have hnn : 0 ≤ᵐ[volume.restrict (B0579.cell d)] fun x : ℝ × ℝ => ε * kFar_K1 d δ * (1 + x.2 ^ 2)⁻¹ :=
    Eventually.of_forall fun x => mul_nonneg
      (mul_nonneg hε.le (kFar_K1_nonneg hd hδ)) (inv_nonneg.2 (by positivity))
  have step2 : ∫ x in B0579.cell d ∩ {x : ℝ × ℝ | δ ≤ ‖x‖}, ε * kFar_K1 d δ * (1 + x.2 ^ 2)⁻¹ ≤
      ∫ x in B0579.cell d, ε * kFar_K1 d δ * (1 + x.2 ^ 2)⁻¹ :=
    setIntegral_mono_set (hint.const_mul (ε * kFar_K1 d δ)) hnn
      (Eventually.of_forall fun x hx => hx.1)
  have step3 : ∫ x in B0579.cell d, ε * kFar_K1 d δ * (1 + x.2 ^ 2)⁻¹ =
      ε * kFar_K1 d δ * ∫ x in B0579.cell d, (1 + x.2 ^ 2)⁻¹ :=
    integral_const_mul _ _
  rw [step3] at step2
  linarith [step1, step2]

end UnforcedLeray.Short.IIIa
