import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4.KcL1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4.Coef

/-!
# `FcvEllUnif`: the uniform bound `|ℓ_r ω| ≤ C ‖ω‖` for `0 < r ≤ T` (source 2819-2836, 4610-4615)

Let `R` be the band radius of the cylinder test `φ`.  The integrand of `ellFn` vanishes off the band
`|η| ≤ R` (`φ`, `pd k φ`, `lapP φ` vanish there, and the `Ec` term is multiplied by `φ`), so the cell
integral is taken over `S = cell ∩ {|η| ≤ R}`.  On `S` the pointwise bound of `FcvEllCoef` (constants
`A`, `B`) gives `‖integrand‖ ≤ A‖xFn ω‖ + B‖kcC ω · 0‖ + B‖kcC ω · 1‖`; the first term is bounded by the
cell `L¹` bound `lintegral_norm_cell_le`, the others by the band `L¹` bound `fcvKcL1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Pointwise bound of the tested integrand `ω·a - (u₀ b₀ + u₁ b₁) p` (complex form of
`UnforcedLeray.Short.IIIa.flowIntegrand`). -/
theorem flow_pt_bound (w u0 u1 : ℂ) (a b0 b1 p A B : ℝ) (ha : |a| ≤ A)
    (hb0 : |b0 * p| ≤ B) (hb1 : |b1 * p| ≤ B) :
    ‖w * (a : ℂ) - (u0 * (b0 : ℂ) + u1 * (b1 : ℂ)) * (p : ℂ)‖ ≤
      A * ‖w‖ + B * ‖u0‖ + B * ‖u1‖ := by
  have hA : ‖(a : ℂ)‖ ≤ A := by rw [Complex.norm_real, Real.norm_eq_abs]; exact ha
  have hB0 : ‖((b0 * p : ℝ) : ℂ)‖ ≤ B := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hb0
  have hB1 : ‖((b1 * p : ℝ) : ℂ)‖ ≤ B := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hb1
  have e : (u0 * (b0 : ℂ) + u1 * (b1 : ℂ)) * (p : ℂ) =
      u0 * ((b0 * p : ℝ) : ℂ) + u1 * ((b1 * p : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  calc ‖w * (a : ℂ) - (u0 * ((b0 * p : ℝ) : ℂ) + u1 * ((b1 * p : ℝ) : ℂ))‖
      ≤ ‖w * (a : ℂ)‖ + ‖u0 * ((b0 * p : ℝ) : ℂ) + u1 * ((b1 * p : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ ‖w‖ * A + (‖u0‖ * B + ‖u1‖ * B) := by
        refine add_le_add ?_ ?_
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hA (norm_nonneg _)
        · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hB0 (norm_nonneg _)
          · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hB1 (norm_nonneg _)
    _ = A * ‖w‖ + B * ‖u0‖ + B * ‖u1‖ := by ring

/-- The norm of the Biot-Savart velocity component is integrable on the band `cell ∩ {|η| ≤ R}`
(`kcLp ω ∈ L²`, finite measure of the band). -/
theorem kcC_norm_integrableOn_band {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (R : ℝ)
    (ω : Xmc c m) (j : Fin 2) :
    IntegrableOn (fun x => ‖kcC ω x j‖) (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R}) := by
  have hSsub : B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R} ⊆ B0579.cell c := inter_subset_left
  have hSfin : volume (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R}) < ∞ := by
    have hK : B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R} ⊆
        Icc (-(c / 2)) (c / 2) ×ˢ Icc (-|R|) |R| := by
      intro y hy
      have h1 := hy.1
      simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at h1
      have h2 : |y.2| ≤ |R| := (hy.2 : |y.2| ≤ R).trans (le_abs_self R)
      exact ⟨⟨h1.1, h1.2.le⟩, abs_le.1 h2⟩
    exact lt_of_le_of_lt (measure_mono hK) ((isCompact_Icc.prod isCompact_Icc).measure_lt_top)
  have hνle : volume.restrict (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R}) ≤ B0581.cellVol c :=
    Measure.restrict_mono hSsub le_rfl
  have : IsFiniteMeasure (volume.restrict (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R})) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hSfin⟩
  have hmem : MemLp (kcLp ω : ℝ × ℝ → Merid) 2
      (volume.restrict (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R})) :=
    (Lp.memLp (kcLp ω)).mono_measure hνle
  have hint : Integrable (kcLp ω : ℝ × ℝ → Merid)
      (volume.restrict (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R})) :=
    hmem.integrable (by norm_num)
  have hae : kcMer ω =ᵐ[volume.restrict (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R})]
      (kcLp ω : ℝ × ℝ → Merid) :=
    ae_restrict_of_ae_restrict_of_subset hSsub (kcMer_ae ω)
  have hm1 : AEStronglyMeasurable (fun x => (((kcLp ω : ℝ × ℝ → Merid) x j : ℝ) : ℂ))
      (volume.restrict (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R})) :=
    (Complex.continuous_ofReal.comp (EuclideanSpace.proj j : Merid →L[ℝ] ℝ).continuous
      ).comp_aestronglyMeasurable hmem.1
  have hmeasC : AEStronglyMeasurable (fun x => kcC ω x j)
      (volume.restrict (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R})) := by
    refine AEStronglyMeasurable.congr hm1 ?_
    filter_upwards [hae] with x hx
    unfold kcC
    rw [hx]
  have hbd : ∀ᵐ x ∂(volume.restrict (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R})),
      ‖kcC ω x j‖ ≤ ‖(kcLp ω : ℝ × ℝ → Merid) x‖ := by
    filter_upwards [hae] with x hx
    unfold kcC
    rw [Complex.norm_real, hx]
    exact PiLp.norm_apply_le _ j
  exact (Integrable.mono' hint.norm hmeasC hbd).norm

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst in
/-- **`FcvEllUnif`**: `|ℓ_r ω| ≤ C ‖ω‖` for `0 < r ≤ T`, uniformly (source 2819-2836, 4610-4615). -/
theorem fcvEllUnif : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FcvEllUnif := by
  unfold FcvEllUnif
  intro ν c m _ _ tr φ hφ T
  obtain ⟨A0, B0, hAB0⟩ := fcvEllCoef ν c tr φ hφ T
  obtain ⟨A, B, hA0, hB0, hAB⟩ : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ r ∈ Icc (0 : ℝ) T,
      ∀ y ∈ B0579.cell c,
        |ν * UnforcedLeray.Short.IIIa.lapP φ y + (tr.v r y 0 * B0579.pd 0 φ y + tr.v r y 1 * B0579.pd 1 φ y)| ≤ A ∧
        ∀ k : Fin 2, |B0579.pd k (UnforcedLeray.B0238.Ec tr r) y * φ y| ≤ B :=
    ⟨max A0 0, max B0 0, le_max_right _ _, le_max_right _ _, fun r hr y hy =>
      ⟨((hAB0 r hr y hy).1).trans (le_max_left _ _),
        fun k => ((hAB0 r hr y hy).2 k).trans (le_max_left _ _)⟩⟩
  -- band radius of `φ`, `pd φ`, `lapP φ`
  obtain ⟨R0, hR0⟩ := hφ.band
  obtain ⟨R1, hR1⟩ := (hφ.pd 0).band
  obtain ⟨R2, hR2⟩ := (hφ.pd 1).band
  obtain ⟨R3, hR3⟩ := ((hφ.pd 0).pd 0).band
  obtain ⟨R4, hR4⟩ := ((hφ.pd 1).pd 1).band
  obtain ⟨Rb, hRb0, hRb1, hRb2, hRb3, hRb4⟩ : ∃ Rb : ℝ, R0 ≤ Rb ∧ R1 ≤ Rb ∧ R2 ≤ Rb ∧
      R3 ≤ Rb ∧ R4 ≤ Rb := ⟨max (max (max R0 R1) (max R2 R3)) R4, by simp [le_max_iff],
        by simp [le_max_iff], by simp [le_max_iff], by simp [le_max_iff], by simp [le_max_iff]⟩
  have hvan : ∀ y : ℝ × ℝ, Rb < |y.2| →
      φ y = 0 ∧ B0579.pd 0 φ y = 0 ∧ B0579.pd 1 φ y = 0 ∧
        B0579.pd 0 (B0579.pd 0 φ) y + B0579.pd 1 (B0579.pd 1 φ) y = 0 := by
    intro y hy
    refine ⟨hR0 y (lt_of_le_of_lt hRb0 hy), hR1 y (lt_of_le_of_lt hRb1 hy),
      hR2 y (lt_of_le_of_lt hRb2 hy), ?_⟩
    rw [hR3 y (lt_of_le_of_lt hRb3 hy), hR4 y (lt_of_le_of_lt hRb4 hy), add_zero]
  -- band `L¹` bound of the Biot-Savart velocity
  obtain ⟨C1, hC1⟩ := fcvKcL1 c m Rb
  refine ⟨A * (B0592.weightConst m).toReal + B * C1 + B * C1, fun r hr0 hrT ω => ?_⟩
  -- the integrand vanishes off the band
  have hzero : ∀ x : ℝ × ℝ, Rb < |x.2| → UnforcedLeray.Short.IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ x = 0 := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := hvan x hx
    have hl : UnforcedLeray.Short.IIIa.lapP φ x = 0 := h4
    simp only [UnforcedLeray.Short.IIIa.flowIntegrand, hl, h1, h2, h3, mul_zero, zero_mul, add_zero, zero_add,
      Complex.ofReal_zero, sub_zero, sub_self]
  have hSm : MeasurableSet (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb}) :=
    (B0579.measurableSet_cell c).inter
      (measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const)
  have hSsub : B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb} ⊆ B0579.cell c := inter_subset_left
  -- step 1: restrict the cell integral to the band
  have e1 : ∫ x in B0579.cell c, ‖UnforcedLeray.Short.IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ x‖ =
      ∫ x in B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb},
        ‖UnforcedLeray.Short.IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ x‖ := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (B0579.measurableSet_cell c) hSsub
      (fun x hx => ?_)
    have hxR : Rb < |x.2| := by
      by_contra h
      exact hx.2 ⟨hx.1, not_lt.1 h⟩
    rw [hzero x hxR, norm_zero]
  -- step 2: pointwise bound on the band
  have hpt : ∀ x ∈ B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb},
      ‖UnforcedLeray.Short.IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ x‖ ≤
        A * ‖xFn ω x‖ + B * ‖kcC ω x 0‖ + B * ‖kcC ω x 1‖ := by
    intro x hx
    obtain ⟨hA1, hB1⟩ := hAB r ⟨hr0.le, hrT⟩ x hx.1
    exact flow_pt_bound (xFn ω x) (kcC ω x 0) (kcC ω x 1)
      (ν * UnforcedLeray.Short.IIIa.lapP φ x + (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x))
      (B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x) (B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x)
      (φ x) A B hA1 (hB1 0) (hB1 1)
  -- integrability of the three majorant terms on the band
  have hI1 : Integrable (fun x => A * ‖xFn ω x‖)
      (volume.restrict (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb})) :=
    Integrable.const_mul (IntegrableOn.mono_set (Integrable.norm (xFn_integrableOn ω)) hSsub) A
  have hI2 : Integrable (fun x => B * ‖kcC ω x 0‖)
      (volume.restrict (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb})) :=
    Integrable.const_mul (kcC_norm_integrableOn_band Rb ω 0) B
  have hI3 : Integrable (fun x => B * ‖kcC ω x 1‖)
      (volume.restrict (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb})) :=
    Integrable.const_mul (kcC_norm_integrableOn_band Rb ω 1) B
  have hmono : ∫ x in B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb},
      ‖UnforcedLeray.Short.IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ x‖ ≤
        ∫ x in B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb},
          (A * ‖xFn ω x‖ + B * ‖kcC ω x 0‖ + B * ‖kcC ω x 1‖) :=
    integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) ((hI1.add hI2).add hI3)
      (ae_restrict_of_forall_mem hSm hpt)
  -- step 3: the three majorant integrals
  have h1 : ∫ x in B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb}, A * ‖xFn ω x‖ ≤
      A * ((B0592.weightConst m).toReal * ‖ω‖) := by
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hA0
    refine le_trans ?_ (lintegral_norm_cell_le ω)
    exact setIntegral_mono_set (Integrable.norm (xFn_integrableOn ω))
      (Eventually.of_forall fun x => norm_nonneg _) hSsub.eventuallyLE
  have h2 : ∫ x in B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb}, B * ‖kcC ω x 0‖ ≤ B * (C1 * ‖ω‖) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hC1 ω 0) hB0
  have h3 : ∫ x in B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb}, B * ‖kcC ω x 1‖ ≤ B * (C1 * ‖ω‖) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hC1 ω 1) hB0
  have hsplit : ∫ x in B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb},
      (A * ‖xFn ω x‖ + B * ‖kcC ω x 0‖ + B * ‖kcC ω x 1‖) =
        (∫ x in B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb}, A * ‖xFn ω x‖) +
        (∫ x in B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb}, B * ‖kcC ω x 0‖) +
        (∫ x in B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb}, B * ‖kcC ω x 1‖) := by
    have hsum : Integrable (fun x => A * ‖xFn ω x‖ + B * ‖kcC ω x 0‖)
        (volume.restrict (B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb})) := hI1.add hI2
    rw [integral_add hsum hI3, integral_add hI1 hI2]
  -- conclusion
  have hfin : ‖ellFn tr φ r ω‖ ≤
      (A * (B0592.weightConst m).toReal + B * C1 + B * C1) * ‖ω‖ := by
    have hnorm : ‖ellFn tr φ r ω‖ ≤ ∫ x in B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ Rb},
        ‖UnforcedLeray.Short.IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ x‖ := by
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← e1]
    have hexp : (A * (B0592.weightConst m).toReal + B * C1 + B * C1) * ‖ω‖ =
        A * ((B0592.weightConst m).toReal * ‖ω‖) + B * (C1 * ‖ω‖) + B * (C1 * ‖ω‖) := by
      ring
    rw [hexp]
    have h4 := hmono.trans_eq hsplit
    linarith [hnorm, h4, h1, h2, h3]
  exact hfin
