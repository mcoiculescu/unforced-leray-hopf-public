import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_2

/-!
# `SFCHeatParamMeas` (decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2`)

Source `the November 2 reference manuscript`
1650-1656, 1684-1689, 3426-3430.  For `0 < σ < s` the heat of the datum `σ⁻¹ G(σ, ·)` and its
derivative are Gaussian integrals (shift moved onto the kernel) of functions jointly measurable
in `(σ, z)`; the parametric integral of a jointly measurable function is a.e.-strongly
measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Gaussian UnforcedLeray.B0224
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem measurable_gaussKernel_two {α : Type*} [MeasurableSpace α] {θ : α → ℝ} {z : α → Euc 2}
    (hθ : Measurable θ) (hz : Measurable z) : Measurable fun a => gaussKernel 2 (θ a) (z a) := by
  unfold gaussKernel
  have h1 : Measurable fun a => ‖z a‖ := hz.norm
  fun_prop

theorem measurable_gradG {α : Type*} [MeasurableSpace α] {θ : α → ℝ} {z : α → Euc 2}
    (hθ : Measurable θ) (hz : Measurable z) : Measurable fun a => gradG (θ a) (z a) := by
  unfold gradG
  have h1 : Measurable fun a => (-(1 / (2 * θ a)) * gaussKernel 2 (θ a) (z a)) := by
    have := measurable_gaussKernel_two hθ hz
    fun_prop
  exact h1.smul ((innerSL ℝ).continuous.measurable.comp hz)


open UnforcedLeray.B0223 in
theorem sfcHeatParamMeas : SFCHeatParamMeas := by
  intro G hG M s0 s ν hM hs0 hGz hν y
  set θ : ℝ → ℝ := fun σ => ν * (s - σ) with hθdef
  have hθm : Measurable θ := by simp only [hθdef]; fun_prop
  have hU : Measurable fun p : ℝ × Euc 2 => (((p.1 : ℝ) : ℂ)⁻¹) • G (p.1, planeι p.2) := by
    have h1 : Measurable fun p : ℝ × Euc 2 => G (p.1, planeι p.2) :=
      hG.measurable.comp (measurable_fst.prodMk (continuous_planeι.measurable.comp measurable_snd))
    have h2 : Measurable fun p : ℝ × Euc 2 => (((p.1 : ℝ) : ℂ)⁻¹) :=
      (Complex.measurable_ofReal.comp measurable_fst).inv
    exact h2.smul h1
  have hae : ∀ᵐ σ ∂(volume.restrict (Ioc 0 s)), σ ∈ Ioo 0 s := by
    have h1 : ∀ᵐ σ ∂(volume.restrict (Ioc 0 s)), σ ∈ Ioc 0 s := ae_restrict_mem measurableSet_Ioc
    have hne : ∀ᵐ σ ∂(volume : Measure ℝ), σ ≠ s := by
      rw [ae_iff]; simp
    have h3 : ∀ᵐ σ ∂(volume.restrict (Ioc 0 s)), σ ≠ s := ae_restrict_of_ae hne
    filter_upwards [h1, h3] with σ h1 h3
    exact ⟨h1.1, lt_of_le_of_ne h1.2 h3⟩
  have hz : Measurable fun p : ℝ × Euc 2 => planeLp y - p.2 :=
    measurable_const.sub measurable_snd
  have hθ1 : Measurable fun p : ℝ × Euc 2 => θ p.1 := hθm.comp measurable_fst
  constructor
  · have hm : AEStronglyMeasurable (fun σ : ℝ => ∫ z : Euc 2,
        gaussKernel 2 (θ σ) (planeLp y - z) • ((((σ : ℝ) : ℂ)⁻¹) • G (σ, planeι z)))
        (volume.restrict (Ioc 0 s)) := by
      refine AEStronglyMeasurable.integral_prod_right'
        (f := fun p : ℝ × Euc 2 => gaussKernel 2 (θ p.1) (planeLp y - p.2) •
          ((((p.1 : ℝ) : ℂ)⁻¹) • G (p.1, planeι p.2))) ?_
      exact ((measurable_gaussKernel_two hθ1 hz).smul hU).aestronglyMeasurable
    refine hm.congr ?_
    filter_upwards [hae] with σ hσ
    exact (planeHeat_eq_shift (mul_pos hν (sub_pos.2 hσ.2))
      (fun z => (((σ : ℝ) : ℂ)⁻¹) • G (σ, z)) y).symm
  · have hcont1 : Continuous (fun A : Euc 2 →L[ℝ] ℝ => A.comp planeLp) :=
      ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) (Euc 2) ℝ).flip planeLp).continuous
    have hA : Measurable fun p : ℝ × Euc 2 =>
        (gradG (θ p.1) (planeLp y - p.2)).comp planeLp :=
      hcont1.measurable.comp (measurable_gradG hθ1 hz)
    have hcont2 : Continuous (fun q : ((ℝ × ℝ) →L[ℝ] ℝ) × MeridC => q.1.smulRight q.2) :=
      (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) MeridC).continuous₂
    have hH : Measurable fun p : ℝ × Euc 2 =>
        ((gradG (θ p.1) (planeLp y - p.2)).comp planeLp).smulRight
          ((((p.1 : ℝ) : ℂ)⁻¹) • G (p.1, planeι p.2)) :=
      Measurable.comp (g := fun q : ((ℝ × ℝ) →L[ℝ] ℝ) × MeridC => q.1.smulRight q.2)
        (f := fun p : ℝ × Euc 2 => ((gradG (θ p.1) (planeLp y - p.2)).comp planeLp,
          (((p.1 : ℝ) : ℂ)⁻¹) • G (p.1, planeι p.2))) hcont2.measurable (hA.prodMk hU)
    have hm := AEStronglyMeasurable.integral_prod_right'
      (μ := volume.restrict (Ioc 0 s)) (ν := (volume : Measure (Euc 2)))
      (f := fun p : ℝ × Euc 2 => ((gradG (θ p.1) (planeLp y - p.2)).comp planeLp).smulRight
          ((((p.1 : ℝ) : ℂ)⁻¹) • G (p.1, planeι p.2))) hH.aestronglyMeasurable
    refine hm.congr ?_
    filter_upwards [hae] with σ hσ
    have hθ : 0 < θ σ := mul_pos hν (sub_pos.2 hσ.2)
    have hσ0 : 0 < σ := hσ.1
    have hc : Continuous fun z : ℝ × ℝ => (((σ : ℝ) : ℂ)⁻¹) • G (σ, z) :=
      Continuous.const_smul (hG.comp (continuous_const.prodMk continuous_id :
        Continuous fun z : ℝ × ℝ => (σ, z))) (((σ : ℝ) : ℂ)⁻¹)
    have hb : ∀ z : ℝ × ℝ, ‖(((σ : ℝ) : ℂ)⁻¹) • G (σ, z)‖ ≤ σ⁻¹ * M := by
      intro z
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hσ0.le]
      exact mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.2 hσ0.le)
    exact (hasFDerivAt_planeHeat hθ hc hb y).fderiv.symm
end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
