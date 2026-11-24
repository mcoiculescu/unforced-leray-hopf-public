import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Band `L¹` bound of the Biot-Savart velocity (the content of `FcvKcL1`)

The cell `B0579.cell c = Ico × univ` has infinite measure, and `‖kcLp ω‖_{L²(cell)} ≤ C‖ω‖` only
(`norm_velocity_le`); so a whole-cell `L¹` bound does not follow by Cauchy-Schwarz.
The tested integrand of `ellFn` is supported in the band `|η| ≤ R` of the cylinder test `φ`
(source 2819-2836), and there Cauchy-Schwarz gives the bound proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem norm_kcLp_le {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ω : Xmc c m) :
    ‖kcLp ω‖ ≤ 5 * (1 + c) * ‖ω‖ := by
  have h1 := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_realBiotSavart_le
    (one_le_of_fact (m := m)) (reX ω.1) (reX_circ ω)
  have h2 : ‖reX ω.1‖ ≤ ‖ω.1‖ := by
    have := ContinuousLinearMap.norm_compLp_le (Complex.reCLM : ℂ →L[ℝ] ℝ) ω.1
    rw [Complex.reCLM_norm, one_mul] at this
    exact this
  have hc : 0 ≤ 5 * (1 + c) := by have := (Fact.out : 0 < c); positivity
  calc ‖kcLp ω‖ ≤ 5 * (1 + c) * ‖reX ω.1‖ := h1
    _ ≤ 5 * (1 + c) * ‖ω.1‖ := mul_le_mul_of_nonneg_left h2 hc
    _ = 5 * (1 + c) * ‖ω‖ := rfl

/-- **Band `L¹` bound** of `K_c ω` on `cell ∩ {|η| ≤ R}` (Cauchy-Schwarz on a set of finite
measure; `norm_velocity_le`). -/
theorem kcL1_band {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (R : ℝ) :
    ∃ C : ℝ, ∀ (ω : Xmc c m) (j : Fin 2),
      ∫ x in B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R}, ‖kcC ω x j‖ ≤ C * ‖ω‖ := by
  set S : Set (ℝ × ℝ) := B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R} with hS
  have hSsub : S ⊆ B0579.cell c := inter_subset_left
  have hSm : MeasurableSet S :=
    (B0579.measurableSet_cell c).inter (measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const)
  have hSfin : volume S < ∞ := by
    have hK : S ⊆ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-|R|) |R| := by
      intro y hy
      have h1 := hy.1
      simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at h1
      have h2 : |y.2| ≤ |R| := hy.2.trans (le_abs_self R)
      exact ⟨⟨h1.1, h1.2.le⟩, abs_le.1 h2⟩
    exact lt_of_le_of_lt (measure_mono hK)
      ((isCompact_Icc.prod isCompact_Icc).measure_lt_top)
  refine ⟨5 * (1 + c) * (volume S).toReal ^ (1 / 2 : ℝ), fun ω j => ?_⟩
  set f : ℝ × ℝ → Merid := (kcLp ω : ℝ × ℝ → Merid) with hf
  set ν : Measure (ℝ × ℝ) := volume.restrict S with hν
  have hνle : ν ≤ B0581.cellVol c := Measure.restrict_mono hSsub le_rfl
  have hνfin : ν univ = volume S := by simp [hν]
  have hae : (fun x => kcC ω x j) =ᵐ[ν] fun x => ((f x j : ℝ) : ℂ) := by
    have h := kcMer_ae ω
    have h' : kcMer ω =ᵐ[ν] f := ae_restrict_of_ae_restrict_of_subset hSsub h
    filter_upwards [h'] with x hx
    show ((kcMer ω x j : ℝ) : ℂ) = _
    rw [hx]
  have hpt : ∀ x, ‖((f x j : ℝ) : ℂ)‖ₑ ≤ ‖f x‖ₑ := by
    intro x
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Complex.norm_real]
    exact PiLp.norm_apply_le (f x) j
  have hmem : MemLp f 2 ν := (Lp.memLp (kcLp ω)).mono_measure hνle
  have hmeas : AEStronglyMeasurable (fun x => kcC ω x j) ν := by
    refine AEStronglyMeasurable.congr ?_ hae.symm
    exact (Complex.continuous_ofReal.comp (EuclideanSpace.proj j : Merid →L[ℝ] ℝ).continuous
      ).comp_aestronglyMeasurable hmem.1
  have e1 : ∫⁻ x, ‖kcC ω x j‖ₑ ∂ν ≤ eLpNorm f 1 ν := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    calc _ = ∫⁻ x, ‖((f x j : ℝ) : ℂ)‖ₑ ∂ν := lintegral_congr_ae (by
            filter_upwards [hae] with x hx; rw [hx])
      _ ≤ _ := lintegral_mono hpt
  have e2 : eLpNorm f 1 ν ≤ eLpNorm f 2 ν * ν univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hmem.1
  have e3 : eLpNorm f 2 ν ≤ ENNReal.ofReal ‖kcLp ω‖ := by
    refine (eLpNorm_mono_measure f hνle).trans ?_
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp (kcLp ω)).eLpNorm_ne_top]
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = 1 / 2 := by
    norm_num
  rw [hexp, hνfin] at e2
  have hfin : ENNReal.ofReal ‖kcLp ω‖ * volume S ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hSfin.ne)
  have e4 : ∫⁻ x, ‖kcC ω x j‖ₑ ∂ν ≤ ENNReal.ofReal ‖kcLp ω‖ * volume S ^ (1 / 2 : ℝ) :=
    e1.trans (e2.trans (by gcongr))
  have hint : ∫ x in S, ‖kcC ω x j‖ = (∫⁻ x, ‖kcC ω x j‖ₑ ∂ν).toReal :=
    integral_norm_eq_lintegral_enorm hmeas
  rw [hint]
  have e5 := ENNReal.toReal_mono hfin e4
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _),
    ← ENNReal.toReal_rpow] at e5
  have hV : 0 ≤ (volume S).toReal ^ (1 / 2 : ℝ) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  calc _ ≤ ‖kcLp ω‖ * (volume S).toReal ^ (1 / 2 : ℝ) := e5
    _ ≤ (5 * (1 + c) * ‖ω‖) * (volume S).toReal ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (norm_kcLp_le ω) hV
    _ = _ := by ring

/-- `FcvKcL1` (band form) from `kcL1_band`. -/
theorem fcvKcL1 : FcvKcL1 := fun _ _ _ _ R => kcL1_band R

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
