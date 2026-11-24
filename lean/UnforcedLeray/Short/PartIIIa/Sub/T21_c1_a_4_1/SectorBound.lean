import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4_1

/-!
# `PartIII-a:T21/c1/a/4/1`: the sector bound leaf `ExtSectorBound`

Source: `the November 2 reference manuscript`
lines 603-610. The circle `r e^{iθ}` is `planeToC (r cos θ, r sin θ)`, so the Gaussian bound on the
plane gives a pointwise bound on the circle; the angular integral over `[0, 2π]` with the unimodular
factor `e^{-inθ}` and the factor `(2π)⁻¹` keeps the same constant. Measurability is
`ParsevalH.stronglyMeasurable_angularSector` applied to `hg.stronglyMeasurable`.
-/

set_option autoImplicit false

open MeasureTheory Real

theorem extSectorBound_proof : UnforcedLeray.Short.IIIa.ExtSectorBound := by
  intro g C n hg hgb
  have hpt : ∀ r : ℝ, 0 ≤ r → ∀ θ : ℝ,
      ‖g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ C * Real.exp (-(r ^ 2) / 8) := by
    intro r hr θ
    have hx : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) =
        UnforcedLeray.Short.IIIa.planeToC (r * Real.cos θ, r * Real.sin θ) := by
      apply Complex.ext
      · simp [UnforcedLeray.Short.IIIa.planeToC, Complex.exp_ofReal_mul_I_re]
      · simp [UnforcedLeray.Short.IIIa.planeToC, Complex.exp_ofReal_mul_I_im]
    have hb : ‖g (UnforcedLeray.Short.IIIa.planeToC (r * Real.cos θ, r * Real.sin θ))‖ ≤
        C * Real.exp (-((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) / 8) :=
      hgb (r * Real.cos θ, r * Real.sin θ)
    have hsq : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
      have h1 := Real.sin_sq_add_cos_sq θ
      calc (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2
          = r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
        _ = r ^ 2 := by rw [h1, mul_one]
    rw [hx]
    rw [hsq] at hb
    exact hb
  have hnorm_e : ∀ θ : ℝ, ‖Complex.exp (-((n : ℂ) * θ * Complex.I))‖ = 1 := by
    intro θ
    rw [Complex.norm_exp]
    simp
  have hint : ∀ r : ℝ, 0 ≤ r →
      ‖UnforcedLeray.Planar.NUE.Polar.angularSector g n r‖ ≤ C * Real.exp (-(r ^ 2) / 8) := by
    intro r hr
    unfold UnforcedLeray.Planar.NUE.Polar.angularSector
    rw [norm_mul]
    have hbd : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * π),
        ‖g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-((n : ℂ) * θ * Complex.I))‖ ≤ C * Real.exp (-(r ^ 2) / 8) := by
      intro θ _
      rw [norm_mul, hnorm_e θ, mul_one]
      exact hpt r hr θ
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    have hpos : 0 < 2 * π := by positivity
    have h2pi : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
      have e : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
      rw [e, ← Complex.ofReal_inv, Complex.norm_real, norm_inv,
        Real.norm_of_nonneg (by positivity)]
    rw [h2pi]
    have hinv : 0 < (2 * π)⁻¹ := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hI hinv.le) (le_of_eq ?_)
    rw [sub_zero, abs_of_pos hpos]
    field_simp
  refine ⟨hint, ?_⟩
  exact UnforcedLeray.Planar.NUE.Ang.ParsevalH.stronglyMeasurable_angularSector hg.stronglyMeasurable n
