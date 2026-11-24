import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_3

/-!
# The `L²(H)` majorant (task `PartIII-b:C/flatset/col/7/3/2/1/2/3/2`)

Source `the November 2 reference manuscript` 1650-1656.  `measureH c` is
`s^{-3/2} ds dq dη` on the cell `s > 0`, `q ∈ (0,c]`, `η ∈ ℝ`.  The function
`C·1_{[a,b]}(s)(1+η²)⁻¹` has square `C²·1_{[a,b]}(s)(1+η²)⁻²`; on `[a,b]` the weight is at most
`a^{-3/2}`, and `(1+η²)⁻²` is integrable, so the square is integrable for `0 < a`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdS pdQ pdEta)

theorem mem_lp_majorant : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.MemLpMajorant := by
  intro c a b C hc ha
  set f : Profile → ℝ := fun p =>
    C * (Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * (1 + p.2.2 ^ 2)⁻¹ with hf_def
  have hind : Measurable (fun p : Profile => (Icc a b).indicator (fun _ => (1 : ℝ)) p.1) :=
    (measurable_const.indicator measurableSet_Icc).comp measurable_fst
  have hinv : Measurable (fun p : Profile => (1 + p.2.2 ^ 2)⁻¹) := by
    fun_prop
  have hfm : Measurable f := (measurable_const.mul hind).mul hinv
  -- the density and the square
  have hflt : ∀ᵐ p ∂(UnforcedLeray.B0220.cellMeasure c),
      UnforcedLeray.B0220.weightH p < ⊤ :=
    Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top
  -- integrable majorant on the whole profile space
  set φ : ℝ → ℝ := (Icc a b).indicator (fun _ => (1 : ℝ)) with hφ_def
  set ψ : ℝ → ℝ := (Icc 0 c).indicator (fun _ => (1 : ℝ)) with hψ_def
  set χ : ℝ → ℝ := fun η => ((1 + η ^ 2)⁻¹) ^ 2 with hχ_def
  have hφ : Integrable φ :=
    (integrable_indicator_iff measurableSet_Icc).2 (continuous_const.integrableOn_Icc)
  have hψ : Integrable ψ :=
    (integrable_indicator_iff measurableSet_Icc).2 (continuous_const.integrableOn_Icc)
  have hχ : Integrable χ := by
    refine integrable_inv_one_add_sq.mono' ?_ ?_
    · exact (by fun_prop : Measurable fun η : ℝ => ((1 + η ^ 2)⁻¹) ^ 2).aestronglyMeasurable
    · refine Eventually.of_forall fun η => ?_
      have ht0 : 0 ≤ (1 + η ^ 2)⁻¹ := by positivity
      have ht1 : (1 + η ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg η])
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
  have hprod1 : Integrable (fun z : ℝ × ℝ => ψ z.1 * χ z.2) := by
    rw [Measure.volume_eq_prod]
    exact hψ.mul_prod hχ
  have hprod2 : Integrable (fun z : ℝ × (ℝ × ℝ) => φ z.1 * (ψ z.2.1 * χ z.2.2)) := by
    rw [Measure.volume_eq_prod]
    exact hφ.mul_prod hprod1
  set K : ℝ := a ^ (-(3 / 2 : ℝ)) * C ^ 2 with hK_def
  set H : Profile → ℝ := fun p => K * (φ p.1 * (ψ p.2.1 * χ p.2.2)) with hH_def
  have hH : Integrable H := hprod2.const_mul K
  -- the pointwise domination on the cell
  have hae : ∀ᵐ p ∂(UnforcedLeray.B0220.cellMeasure c), p ∈ UnforcedLeray.B0220.cell c :=
    ae_restrict_mem (UnforcedLeray.B0220.measurableSet_cell c)
  have hdom : ∀ᵐ p ∂(UnforcedLeray.B0220.cellMeasure c),
      ‖(UnforcedLeray.B0220.weightH p).toReal • (f p ^ 2)‖ ≤ H p := by
    filter_upwards [hae] with p hp
    obtain ⟨hs, hq, -⟩ := hp
    have hs' : 0 < p.1 := hs
    have hq' : p.2.1 ∈ Icc 0 c := Ioc_subset_Icc_self hq
    have hw : (UnforcedLeray.B0220.weightH p).toReal = p.1 ^ (-(3 / 2 : ℝ)) := by
      unfold UnforcedLeray.B0220.weightH
      exact ENNReal.toReal_ofReal (Real.rpow_nonneg hs'.le _)
    rw [hw, Real.norm_of_nonneg (by positivity)]
    by_cases hab : p.1 ∈ Icc a b
    · have hpow : p.1 ^ (-(3 / 2 : ℝ)) ≤ a ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ha hab.1 (by norm_num)
      have hφp : φ p.1 = 1 := indicator_of_mem hab _
      have hψp : ψ p.2.1 = 1 := indicator_of_mem hq' _
      simp only [hf_def, H, hφp, hψp, smul_eq_mul]
      have hsq : 0 ≤ ((1 + p.2.2 ^ 2)⁻¹) ^ 2 := by positivity
      have hpos : 0 ≤ p.1 ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs'.le _
      have hsqC : (C * 1 * (1 + p.2.2 ^ 2)⁻¹) ^ 2 = C ^ 2 * ((1 + p.2.2 ^ 2)⁻¹) ^ 2 := by ring
      rw [hK_def, hsqC]
      have hCsq : 0 ≤ C ^ 2 := sq_nonneg C
      have : p.1 ^ (-(3 / 2 : ℝ)) * (C ^ 2 * ((1 + p.2.2 ^ 2)⁻¹) ^ 2) ≤
          a ^ (-(3 / 2 : ℝ)) * C ^ 2 * (1 * (1 * ((1 + p.2.2 ^ 2)⁻¹) ^ 2)) := by
        have h0 : 0 ≤ C ^ 2 * ((1 + p.2.2 ^ 2)⁻¹) ^ 2 := mul_nonneg hCsq hsq
        nlinarith [mul_le_mul_of_nonneg_right hpow h0]
      exact this
    · have hφp : φ p.1 = 0 := indicator_of_notMem hab _
      simp [hf_def, H, hφp]
  refine (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).2 ?_
  unfold measureH
  rw [integrable_withDensity_iff_integrable_smul' UnforcedLeray.B0220.measurable_weightH hflt]
  refine Integrable.mono' (hH.restrict) ?_ hdom
  exact ((ENNReal.measurable_toReal.comp UnforcedLeray.B0220.measurable_weightH).smul
    (hfm.pow_const 2)).aestronglyMeasurable

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
