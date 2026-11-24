import UnforcedLeray.Analysis.SobolevEmbedding.H1
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
# The energy-class spatial interpolation inequality in three dimensions

Hölder applied to the actual squared and sixth-power norm densities gives
L²--L⁶ interpolation at exponent 10/3. The genuine weak H¹ Sobolev theorem
then supplies L^(10/3) membership and the quantitative energy estimate.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace UnforcedLeray.EnergyInterpolation

/-- Hölder interpolation on the actual nonnegative norm-power integrals. -/
theorem lintegral_ten_thirds_le {f : SpatialField}
    (hf : AEStronglyMeasurable f volume) :
    (∫⁻ x : Space, ‖f x‖ₑ ^ (10 / 3 : ℝ)) ≤
      eLpNorm f 2 volume ^ (4 / 3 : ℝ) * eLpNorm f 6 volume ^ 2 := by
  have h := ENNReal.lintegral_mul_norm_pow_le
    (f := fun x : Space => ‖f x‖ₑ ^ (2 : ℝ))
    (g := fun x : Space => ‖f x‖ₑ ^ (6 : ℝ))
    (hf.enorm.pow_const _) (hf.enorm.pow_const _)
    (p := (2 / 3 : ℝ)) (q := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have he (x : Space) :
      (‖f x‖ₑ ^ (2 : ℝ)) ^ (2 / 3 : ℝ) *
        (‖f x‖ₑ ^ (6 : ℝ)) ^ (1 / 3 : ℝ) = ‖f x‖ₑ ^ (10 / 3 : ℝ) := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have htwo : (∫⁻ x : Space, ‖f x‖ₑ ^ (2 : ℝ)) = eLpNorm f 2 volume ^ (2 : ℝ) := by
    simpa using (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume)
      (p := (2 : ℝ≥0)) (by norm_num)).symm
  have hsix : (∫⁻ x : Space, ‖f x‖ₑ ^ (6 : ℝ)) = eLpNorm f 6 volume ^ (6 : ℝ) := by
    simpa using (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume)
      (p := (6 : ℝ≥0)) (by norm_num)).symm
  simp only [he] at h
  simp only [htwo, hsix, ← ENNReal.rpow_mul] at h
  norm_num at h ⊢
  exact h

/-- The actual weak derivatives give the energy interpolation bound in
extended norms, with no finite-L^(10/3) premise. -/
theorem weak_lintegral_ten_thirds_le {f : SpatialField} {g : Fin 3 → SpatialField}
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hderiv : ∀ i, HasWeakSpatialDerivative i f (g i)) :
    (∫⁻ x : Space, ‖f x‖ₑ ^ (10 / 3 : ℝ)) ≤
      (SobolevEmbedding.sobolevConstant : ℝ≥0∞) ^ 2 *
        eLpNorm f 2 volume ^ (4 / 3 : ℝ) *
        (∑ i : Fin 3, eLpNorm (g i) 2 volume) ^ 2 := by
  have hs := SobolevEmbedding.weak_eLpNorm_six_le_sum hf hg hderiv
  calc
    _ ≤ eLpNorm f 2 volume ^ (4 / 3 : ℝ) * eLpNorm f 6 volume ^ 2 :=
      lintegral_ten_thirds_le hf.aestronglyMeasurable
    _ ≤ eLpNorm f 2 volume ^ (4 / 3 : ℝ) *
        ((SobolevEmbedding.sobolevConstant : ℝ≥0∞) *
          ∑ i : Fin 3, eLpNorm (g i) 2 volume) ^ 2 := by gcongr
    _ = _ := by rw [mul_pow]; ac_rfl

/-- The controlling energy expression is finite from the actual L² hypotheses. -/
theorem energy_majorant_ne_top {f : SpatialField} {g : Fin 3 → SpatialField}
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume) :
    (SobolevEmbedding.sobolevConstant : ℝ≥0∞) ^ 2 *
        eLpNorm f 2 volume ^ (4 / 3 : ℝ) *
        (∑ i : Fin 3, eLpNorm (g i) 2 volume) ^ 2 ≠ ⊤ := by
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hf.2.ne))
    (ENNReal.pow_ne_top (ENNReal.sum_lt_top.mpr (fun i _ => (hg i).2)).ne)

/-- Genuine finite L^(10/3) membership, rather than only a formal norm expression. -/
theorem weak_memLp_ten_thirds {f : SpatialField} {g : Fin 3 → SpatialField}
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hderiv : ∀ i, HasWeakSpatialDerivative i f (g i)) :
    MemLp f (10 / 3 : ℝ≥0∞) volume := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by finiteness)).mpr
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
  exact (weak_lintegral_ten_thirds_le hf hg hderiv).trans_lt
    (lt_top_iff_ne_top.mpr (energy_majorant_ne_top hf hg))

/-- The literal scalar density used in spacetime energy interpolation is integrable. -/
theorem integrable_norm_ten_thirds {f : SpatialField} {g : Fin 3 → SpatialField}
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hderiv : ∀ i, HasWeakSpatialDerivative i f (g i)) :
    Integrable (fun x : Space => ‖f x‖ ^ (10 / 3 : ℝ)) volume := by
  simpa using (integrable_norm_rpow_iff (p := (10 / 3 : ℝ≥0∞))
    hf.aestronglyMeasurable (by norm_num) (by finiteness)).mpr
      (weak_memLp_ten_thirds hf hg hderiv)

/-- The three-dimensional Gagliardo--Nirenberg bound in the exact powers
required by the energy class. Its derivative norm is the coordinate sum. -/
theorem integral_norm_ten_thirds_le {f : SpatialField} {g : Fin 3 → SpatialField}
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hderiv : ∀ i, HasWeakSpatialDerivative i f (g i)) :
    (∫ x : Space, ‖f x‖ ^ (10 / 3 : ℝ)) ≤
      (SobolevEmbedding.sobolevConstant : ℝ) ^ 2 *
        l2Norm f ^ (4 / 3 : ℝ) * (∑ i : Fin 3, l2Norm (g i)) ^ 2 := by
  have h := ENNReal.toReal_mono (energy_majorant_ne_top hf hg)
    (weak_lintegral_ten_thirds_le hf hg hderiv)
  have he : (∫⁻ x : Space, ‖f x‖ₑ ^ (10 / 3 : ℝ)).toReal =
      ∫ x : Space, ‖f x‖ ^ (10 / 3 : ℝ) := by
    have hi := integral_toReal (hf.aestronglyMeasurable.enorm.pow_const (10 / 3 : ℝ))
      (Filter.Eventually.of_forall (fun x : Space =>
        ENNReal.rpow_lt_top_of_nonneg (by norm_num) (enorm_ne_top : ‖f x‖ₑ ≠ ⊤)))
    simpa only [← ENNReal.toReal_rpow, toReal_enorm] using hi.symm
  rw [he] at h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
    ← ENNReal.toReal_rpow, ENNReal.toReal_sum (fun i _ => (hg i).2.ne), l2Norm] using h

/-- The literal scalar integral is exactly the 10/3 power of the finite
L^(10/3) norm whenever membership is available to establish finiteness. -/
theorem integral_norm_ten_thirds_eq_rpow_eLpNorm {f : SpatialField}
    (hf : AEStronglyMeasurable f volume) :
    (∫ x : Space, ‖f x‖ ^ (10 / 3 : ℝ)) =
      (eLpNorm f (10 / 3 : ℝ≥0∞) volume).toReal ^ (10 / 3 : ℝ) := by
  have ht := integral_toReal (hf.enorm.pow_const (10 / 3 : ℝ))
    (Filter.Eventually.of_forall (fun x : Space =>
      ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 10 / 3)
        (enorm_ne_top : ‖f x‖ₑ ≠ ⊤)))
  have he : (∫ x : Space, ‖f x‖ ^ (10 / 3 : ℝ)) =
      (∫⁻ x : Space, ‖f x‖ₑ ^ (10 / 3 : ℝ)).toReal := by
    simpa only [← ENNReal.toReal_rpow, toReal_enorm] using ht
  rw [he]
  have h := eLpNorm_nnreal_pow_eq_lintegral
    (f := f) (μ := volume) (p := (10 / 3 : ℝ≥0)) (by norm_num)
  norm_num only [NNReal.coe_div, NNReal.coe_ofNat, ENNReal.coe_div, ENNReal.coe_ofNat] at h
  rw [← h, ← ENNReal.toReal_rpow]

/-- The Gagliardo--Nirenberg inequality in norm-power form, paired with
`weak_memLp_ten_thirds` to ensure the norm is genuinely finite. -/
theorem weak_norm_ten_thirds_rpow_le {f : SpatialField} {g : Fin 3 → SpatialField}
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hderiv : ∀ i, HasWeakSpatialDerivative i f (g i)) :
    (eLpNorm f (10 / 3 : ℝ≥0∞) volume).toReal ^ (10 / 3 : ℝ) ≤
      (SobolevEmbedding.sobolevConstant : ℝ) ^ 2 *
        l2Norm f ^ (4 / 3 : ℝ) * (∑ i : Fin 3, l2Norm (g i)) ^ 2 := by
  rw [← integral_norm_ten_thirds_eq_rpow_eLpNorm hf.aestronglyMeasurable]
  exact integral_norm_ten_thirds_le hf hg hderiv

end UnforcedLeray.EnergyInterpolation
