import UnforcedLeray.Analysis.Heat.Solenoidal
import UnforcedLeray.Analysis.LerayProjection.TranslationL2

/-!
# Symmetry of the actual heat semigroup

The literal Gaussian is even. Reflection of its Bochner translation integral
therefore moves heat evolution between the two Hilbert inner-product slots.
The argument also gives symmetry for every actual even scalar L¹ kernel.
-/
noncomputable section
open MeasureTheory
namespace UnforcedLeray.Heat

/-- Moving the concrete heat-convention translation reverses its shift. -/
theorem inner_translation_left (a : Space) (u v : L2Space) :
    inner ℝ (translation a u) v = inner ℝ u (translation (-a) v) := by
  simp only [translation_eq_leray_apply, Leray.inner_translation_left, neg_neg]

/-- The standard Gaussian is even, without a restriction on its parameter. -/
theorem kernel_neg (t : ℝ) (x : Space) : kernel t (-x) = kernel t x := by
  simp only [kernel, Gaussian.kernel, norm_neg]

/-- An actual even L¹ convolution is symmetric on the actual L² Hilbert space. -/
theorem convolutionOperator_inner (k : Space → ℝ) (hk : Integrable k volume)
    (heven : ∀ x, k (-x) = k x) (u v : L2Space) :
    inner ℝ (convolutionOperator k hk u) v =
      inner ℝ u (convolutionOperator k hk v) := by
  rw [convolutionOperator_eq_integral_translationOrbit,
    convolutionOperator_eq_integral_translationOrbit]
  calc
    inner ℝ (∫ y : Space, k y • translation y u) v =
        ∫ y : Space, inner ℝ (k y • translation y u) v := by
      simpa only [real_inner_comm] using
        (integral_inner (convolutionOrbit_integrable k hk u) v).symm
    _ = ∫ y : Space, inner ℝ u (k y • translation (-y) v) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [real_inner_smul_left, inner_translation_left, real_inner_smul_right]
    _ = ∫ y : Space, inner ℝ u (k y • translation y v) := by
      have h := integral_neg_eq_self
        (fun y : Space => inner ℝ u (k y • translation y v)) volume
      simpa only [heven] using h
    _ = inner ℝ u (∫ y : Space, k y • translation y v) :=
      integral_inner (convolutionOrbit_integrable k hk v) u

/-- The actual heat semigroup is self-adjoint, including its value at zero. -/
theorem heatOperator_inner (t : ℝ) (u v : L2Space) :
    inner ℝ (heatOperator t u) v = inner ℝ u (heatOperator t v) := by
  by_cases ht : 0 < t
  · rw [heatOperator_pos ht]
    exact convolutionOperator_inner (kernel t) (kernel_integrable ht) (kernel_neg t) u v
  · rw [heatOperator_nonpos (le_of_not_gt ht)]
    rfl

end UnforcedLeray.Heat
