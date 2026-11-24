import UnforcedLeray.Analysis.Heat.ConvolutionPairing
import UnforcedLeray.Analysis.Heat.Translation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Convolution as an actual Bochner integral of translations

The translation orbit is integrated in the ordinary Hilbert L² space.
Pairings, justified by actual integrability and Fubini, identify it with the
raw spatial convolution quotient. Point evaluation on L² is not used.
-/
noncomputable section
open MeasureTheory Filter
namespace UnforcedLeray.Heat

/-- An L¹ kernel gives a genuinely integrable L²-valued translation orbit. -/
theorem convolutionOrbit_integrable (k : Space → ℝ) (hk : Integrable k volume)
    (u : L2Space) : Integrable (fun y : Space => k y • translation y u) := by
  apply (hk.norm.mul_const ‖u‖).mono'
    (hk.aestronglyMeasurable.smul (translation_continuous u).aestronglyMeasurable)
  filter_upwards [] with y
  change ‖k y • translation y u‖ ≤ ‖k y‖ * ‖u‖
  rw [norm_smul, norm_translation]

/-- Integrating the genuine L² orbit gives the expected iterated pairing. -/
theorem integral_translationOrbit_inner (k : Space → ℝ) (hk : Integrable k volume)
    (u v : L2Space) :
    inner ℝ (∫ y : Space, k y • translation y u) v =
      ∫ y : Space, k y * ∫ x : Space, inner ℝ (u (x-y)) (v x) := by
  calc
    inner ℝ (∫ y : Space, k y • translation y u) v =
        inner ℝ v (∫ y : Space, k y • translation y u) := real_inner_comm _ _
    _ = ∫ y : Space, inner ℝ v (k y • translation y u) :=
      (integral_inner (convolutionOrbit_integrable k hk u) v).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [real_inner_smul_right, real_inner_comm (translation y u) v,
        inner_translation_eq_integral]

/-- The actual spatial convolution quotient equals the genuine Hilbert Bochner orbit integral. -/
theorem convolutionOperator_eq_integral_translationOrbit (k : Space → ℝ)
    (hk : Integrable k volume) (u : L2Space) :
    convolutionOperator k hk u = ∫ y : Space, k y • translation y u := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_convolutionOperator_eq_integral hk u v,
    integral_translationOrbit_inner k hk u v]

/-- The Bochner orbit has the literal convolution as its a.e. representative. -/
theorem integral_translationOrbit_rep (k : Space → ℝ) (hk : Integrable k volume)
    (u : L2Space) :
    ((∫ y : Space, k y • translation y u : L2Space) : SpatialField) =ᵐ[volume] convolution k u := by
  rw [← convolutionOperator_eq_integral_translationOrbit k hk u]
  exact convolutionToL2_rep k hk u

/-- The actual convolution operator commutes with every spatial L² translation. -/
theorem convolutionOperator_translation (k : Space → ℝ) (hk : Integrable k volume)
    (a : Space) (u : L2Space) :
    convolutionOperator k hk (translation a u) = translation a (convolutionOperator k hk u) := by
  rw [convolutionOperator_eq_integral_translationOrbit,
    convolutionOperator_eq_integral_translationOrbit]
  calc
    (∫ y : Space, k y • translation y (translation a u)) =
        ∫ y : Space, (translation a).toContinuousLinearMap (k y • translation y u) := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [LinearIsometry.coe_toContinuousLinearMap, map_smul,
        translation_add, add_comm y a]
    _ = _ := (translation a).toContinuousLinearMap.integral_comp_comm
      (convolutionOrbit_integrable k hk u)

end UnforcedLeray.Heat
