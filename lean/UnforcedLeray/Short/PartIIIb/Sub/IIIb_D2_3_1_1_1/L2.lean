import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1

/-!
# `SepWCongrAE` (PartIII-b:IIIb-D2/3/1/1/1, leaf L2)

Source of record: `the November 2 reference manuscript` 3611-3621 (`sep:resolvent`),
`IIIa.sepW` in `Short/PartIII-a/SeparatedKernels.lean`.
The separated response only sees the a.e. class of the source: for a.e. phase `t` the slices
agree a.e. in `z` (Fubini), the bad phases form a null set, and the map `l ↦ τ + 2 log l` pulls
null sets of phases back to null sets of `l ∈ (0, 1)` (its inverse `t ↦ exp((t - τ)/2)` is
locally Lipschitz, so it maps null sets to null sets).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem sepWCongrAE : SepWCongrAE := by
  intro ν μ T₁ T₂ hT y τ
  have hτ : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure Space),
      T₁ t z = T₂ t z :=
    Measure.ae_ae_of_ae_prod hT
  have hNt0 : (volume : Measure ℝ) {t : ℝ | ¬ ∀ᵐ z ∂(volume : Measure Space),
      T₁ t z = T₂ t z} = 0 :=
    ae_iff.1 hτ
  -- the phases `τ + 2 log l`, `l ∈ (0,1)`, are a.e. good
  have hl : ∀ᵐ l ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)),
      ∀ᵐ z ∂(volume : Measure Space), T₁ (τ + 2 * Real.log l) z = T₂ (τ + 2 * Real.log l) z := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    have hsub : {l : ℝ | ¬ (l ∈ Ioo (0 : ℝ) 1 → ∀ᵐ z ∂(volume : Measure Space),
        T₁ (τ + 2 * Real.log l) z = T₂ (τ + 2 * Real.log l) z)}
        ⊆ (fun t : ℝ => Real.exp ((t - τ) / 2)) ''
          {t : ℝ | ¬ ∀ᵐ z ∂(volume : Measure Space), T₁ t z = T₂ t z} := by
      intro l hl
      obtain ⟨hI, hbad⟩ := not_imp.1 hl
      refine ⟨τ + 2 * Real.log l, hbad, ?_⟩
      show Real.exp ((τ + 2 * Real.log l - τ) / 2) = l
      rw [show (τ + 2 * Real.log l - τ) / 2 = Real.log l by ring, Real.exp_log hI.1]
    have hfnull : (volume : Measure ℝ) ((fun t : ℝ => Real.exp ((t - τ) / 2)) ''
        {t : ℝ | ¬ ∀ᵐ z ∂(volume : Measure Space), T₁ t z = T₂ t z}) = 0 :=
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        (by fun_prop) hNt0
    exact ae_iff.2 (measure_mono_null hsub hfnull)
  unfold IIIa.sepW
  funext i
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hl] with l hl'
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hl'] with z hz
  simp only [hz]

end UnforcedLeray.Short.PartIIIb.Concrete
