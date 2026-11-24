import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4.WardBin
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Isos

/-!
# Gained bin norm to ungained bin norm (source 5141-5143, 2683-2689)

`bodyMeasure = π g⁻² ageμ(-3/2)`; on a bin with `g⁻¹ ≤ G` the gained bin norm is at most
`√π G` times the ungained bin `L²` norm of a representative.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ginv_nonneg_bin (γ ν : ℝ) (p : Chart) : 0 ≤ ginv γ ν p := by
  unfold ginv UnforcedLeray.Short.IIIa.gainG
  exact inv_nonneg.2 (Real.exp_pos _).le

theorem binNormToAge : BinNormToAge := by
  intro c γ ν S h j φ F G hφF hG hGb
  have hBm : MeasurableSet (binSet S h j) := by
    unfold binSet
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  have hfin : eLpNorm (φ : Chart → Merid) 2 ((bodyMeasure c γ ν).restrict (binSet S h j)) ≠ ⊤ := by
    have h1 : eLpNorm (φ : Chart → Merid) 2 (bodyMeasure c γ ν) < ⊤ :=
      (Lp.memLp φ).eLpNorm_lt_top
    exact ne_top_of_le_ne_top h1.ne (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hofReal : ENNReal.ofReal (binNorm c γ ν S h j φ)
      = eLpNorm (φ : Chart → Merid) 2 ((bodyMeasure c γ ν).restrict (binSet S h j)) :=
    ENNReal.ofReal_toReal hfin
  have hcongr : eLpNorm (φ : Chart → Merid) 2 ((bodyMeasure c γ ν).restrict (binSet S h j))
      = eLpNorm F 2 ((bodyMeasure c γ ν).restrict (binSet S h j)) :=
    eLpNorm_congr_ae (ae_restrict_of_ae hφF)
  have hC : ∀ μ' : Measure Chart,
      eLpNorm F 2 μ' = (∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ) ∂μ') ^ (1 / 2 : ℝ) := by
    intro μ'
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  have hD : Measurable fun p : Chart => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((NearInst.ginv_measurable' γ ν).pow_const 2).const_mul Real.pi)
  have hbody : (bodyMeasure c γ ν).restrict (binSet S h j)
      = ((ageμ c (-3 / 2)).restrict (binSet S h j)).withDensity
          (fun p : Chart => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2)) := by
    unfold bodyMeasure
    exact restrict_withDensity hBm _
  have hint : ∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ) ∂((bodyMeasure c γ ν).restrict (binSet S h j))
      = ∫⁻ p, (fun p : Chart => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2)) p * ‖F p‖ₑ ^ (2 : ℝ)
          ∂((ageμ c (-3 / 2)).restrict (binSet S h j)) := by
    rw [hbody]
    exact lintegral_withDensity_eq_lintegral_mul_non_measurable _ hD
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
  have hle : ∫⁻ p, (fun p : Chart => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2)) p * ‖F p‖ₑ ^ (2 : ℝ)
          ∂((ageμ c (-3 / 2)).restrict (binSet S h j))
      ≤ ENNReal.ofReal (Real.pi * G ^ 2) * ∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ)
          ∂((ageμ c (-3 / 2)).restrict (binSet S h j)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hBm] with p hp
    have hD' : ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) ≤ ENNReal.ofReal (Real.pi * G ^ 2) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (by nlinarith [hGb p hp, ginv_nonneg_bin γ ν p]) Real.pi_pos.le)
    gcongr
  have hA2 : ENNReal.ofReal (Real.pi * G ^ 2) = ENNReal.ofReal (Real.sqrt Real.pi * G) ^ (2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hG) (by norm_num),
      Real.rpow_two]
    congr 1
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
  calc ENNReal.ofReal (binNorm c γ ν S h j φ)
      = (∫⁻ p, (fun p : Chart => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2)) p * ‖F p‖ₑ ^ (2 : ℝ)
          ∂((ageμ c (-3 / 2)).restrict (binSet S h j))) ^ (1 / 2 : ℝ) := by
        rw [hofReal, hcongr, hC, hint]
    _ ≤ (ENNReal.ofReal (Real.pi * G ^ 2) * ∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ)
          ∂((ageμ c (-3 / 2)).restrict (binSet S h j))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hle (by norm_num)
    _ = (ENNReal.ofReal (Real.sqrt Real.pi * G) ^ (2 : ℝ) * ∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ)
          ∂((ageμ c (-3 / 2)).restrict (binSet S h j))) ^ (1 / 2 : ℝ) := by
        rw [← hA2]
    _ = ENNReal.ofReal (Real.sqrt Real.pi * G) * (∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ)
          ∂((ageμ c (-3 / 2)).restrict (binSet S h j))) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num
    _ = ENNReal.ofReal (Real.sqrt Real.pi * G) * ageNormBin c S h j F := rfl

end UnforcedLeray.Short.PartIIIb.Concrete

end
