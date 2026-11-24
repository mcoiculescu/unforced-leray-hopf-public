import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.SliceLoc

/-!
# Part III-a, task `PartIII-a:T18/3/2/6` (youngSlice): Young inequality on slices

Source: `the November 2 reference manuscript` lines 3541-3552.
For `c > 0`, measurable tensor fields `F, G` with `tnorm2²` locally finite on `(0,∞) × cell c`,
`θ > 0` and a.e. `s > 0`: `2∫_cell |F||G| ≤ θ∫_cell |G|² + θ⁻¹∫_cell |F|²`.
Proof: `SliceLoc` gives a.e. slice integrability of `|F|²`, `|G|²`; the pointwise
`2xy ≤ θy² + θ⁻¹x²`, `integral_mono_of_nonneg`, `integral_add`, `integral_const_mul`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Pointwise Young inequality `2ab ≤ θ b² + θ⁻¹ a²` for `θ > 0`. -/
theorem young_pointwise_slice {θ a b : ℝ} (hθ : 0 < θ) :
    2 * (a * b) ≤ θ * b ^ 2 + θ⁻¹ * a ^ 2 := by
  have hinv : θ⁻¹ * θ = 1 := inv_mul_cancel₀ hθ.ne'
  have key : 0 ≤ θ⁻¹ * (θ * b - a) ^ 2 := mul_nonneg (inv_nonneg.2 hθ.le) (sq_nonneg _)
  have e : θ⁻¹ * (θ * b - a) ^ 2 = θ * b ^ 2 + θ⁻¹ * a ^ 2 - 2 * (a * b) := by
    linear_combination (θ * b ^ 2 - 2 * a * b) * hinv
  linarith [key, e]

theorem youngSlice : UnforcedLeray.Short.IIIa.YoungSlice := by
  intro c F G hc hFm hGm hFi hGi θ hθ
  have hFsq : Measurable fun p : ℝ × (ℝ × ℝ) => tnorm2 (F p) ^ 2 :=
    (measurable_tnorm2 hFm).pow_const 2
  have hGsq : Measurable fun p : ℝ × (ℝ × ℝ) => tnorm2 (G p) ^ 2 :=
    (measurable_tnorm2 hGm).pow_const 2
  have hF0 : ∀ p : ℝ × (ℝ × ℝ), 0 ≤ tnorm2 (F p) ^ 2 := fun p => sq_nonneg _
  have hG0 : ∀ p : ℝ × (ℝ × ℝ), 0 ≤ tnorm2 (G p) ^ 2 := fun p => sq_nonneg _
  filter_upwards [(sliceLoc c _ hc hFsq hF0 hFi).2.2, (sliceLoc c _ hc hGsq hG0 hGi).2.2]
    with s hsF hsG
  have hsF' : Integrable (fun x : ℝ × ℝ => tnorm2 (F (s, x)) ^ 2) (volume.restrict (B0579.cell c)) :=
    hsF
  have hsG' : Integrable (fun x : ℝ × ℝ => tnorm2 (G (s, x)) ^ 2) (volume.restrict (B0579.cell c)) :=
    hsG
  simp only [sliceSq]
  have e1 : ∫ x in B0579.cell c, 2 * (tnorm2 (F (s, x)) * tnorm2 (G (s, x))) =
      2 * ∫ x in B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x)) :=
    integral_const_mul _ _
  have e2 : ∫ x in B0579.cell c, (θ * tnorm2 (G (s, x)) ^ 2 + θ⁻¹ * tnorm2 (F (s, x)) ^ 2) =
      (θ * ∫ x in B0579.cell c, tnorm2 (G (s, x)) ^ 2) +
        (θ⁻¹ * ∫ x in B0579.cell c, tnorm2 (F (s, x)) ^ 2) := by
    rw [integral_add (hsG'.const_mul θ) (hsF'.const_mul θ⁻¹), integral_const_mul,
      integral_const_mul]
  have hint : ∫ x in B0579.cell c, 2 * (tnorm2 (F (s, x)) * tnorm2 (G (s, x))) ≤
      ∫ x in B0579.cell c, (θ * tnorm2 (G (s, x)) ^ 2 + θ⁻¹ * tnorm2 (F (s, x)) ^ 2) := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun x => by unfold tnorm2; positivity
    · exact (hsG'.const_mul θ).add (hsF'.const_mul θ⁻¹)
    · exact Filter.Eventually.of_forall fun x => young_pointwise_slice hθ
  rw [e1, e2] at hint
  exact hint

end UnforcedLeray.Short.IIIa
