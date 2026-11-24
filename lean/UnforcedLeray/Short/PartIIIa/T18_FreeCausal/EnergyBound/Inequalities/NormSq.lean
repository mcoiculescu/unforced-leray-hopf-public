import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_3_2

/-!
# Part III-a, task `PartIII-a:T18/3/2/4` (normSq): the `𝓗`, `𝒯` norms squared as `∫⁻`

Source: `the November 2 reference manuscript` lines 3541-3552.
`eLpNorm_eq_lintegral_rpow_enorm_toReal` at `p = 2`, `enorm` of a nonnegative real is `ofReal`,
and `((∫⁻ …)^(1/2))^2 = ∫⁻ …`. Unfolds `hCalNorm` and `tCalNorm` (FlatCausal.lean).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The square of the `L²` norm of a nonnegative real function is the `∫⁻` of its square. -/
theorem eLpNorm_two_sq_eq_lintegral_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : α → ℝ) (hF : ∀ x, 0 ≤ F x) :
    eLpNorm F 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂μ := by
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  rw [show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (hF x), ENNReal.ofReal_rpow_of_nonneg (hF x) (by norm_num),
    Real.rpow_two]

theorem normSq : UnforcedLeray.Short.IIIa.NormSq := by
  refine ⟨fun c f => ?_, fun c T => ?_⟩
  · unfold hCalNorm
    exact eLpNorm_two_sq_eq_lintegral_nonneg _ (fun p => vnorm2 (f p)) (fun p => Real.sqrt_nonneg _)
  · unfold tCalNorm
    exact eLpNorm_two_sq_eq_lintegral_nonneg _ (fun p => tnorm2 (T p)) (fun p => Real.sqrt_nonneg _)

end UnforcedLeray.Short.IIIa
