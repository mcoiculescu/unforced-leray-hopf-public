import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H1

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (2): the radial integral of the order-four kernel

Source of record: `the November 2 reference manuscript` (73 pages), 3687-3697:
"the radial integral of the order-four kernel is bounded by `C(D² + |z - z_src|²)^{-1}`".
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The vertical profile `M(w) = ((r₀ + D)/(2D)) (D² + w²)⁻¹`. -/
def w2M (r0 D : ℝ) (w : ℝ) : ℝ := (r0 + D) / D / 2 * (D ^ 2 + w ^ 2)⁻¹

/-- **Radial integral**: for `r ≥ r₀ + D`, `∫_r^∞ ρ ((ρ - r₀)² + w²)⁻² dρ ≤ M(w)`. -/
theorem w2_radial {r0 D r : ℝ} (hr0 : 0 ≤ r0) (hD : 0 < D) (hr : r0 + D ≤ r) (w : ℝ) :
    ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ * (((ρ - r0) ^ 2 + w ^ 2)⁻¹) ^ 2) ≤
      ENNReal.ofReal (w2M r0 D w) := by
  set κ : ℝ := (r0 + D) / D with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set g : ℝ → ℝ := fun ρ => -(1 / 2) * ((ρ - r0) ^ 2 + w ^ 2)⁻¹ with hg
  set g' : ℝ → ℝ := fun ρ => (ρ - r0) * (((ρ - r0) ^ 2 + w ^ 2)⁻¹) ^ 2 with hg'
  have hpos : ∀ ρ, r ≤ ρ → 0 < (ρ - r0) ^ 2 + w ^ 2 := fun ρ hρ => by
    have : 0 < ρ - r0 := by linarith
    positivity
  have hder : ∀ ρ ∈ Ioi r, HasDerivAt g (g' ρ) ρ := by
    intro ρ hρ
    have hρ' : r ≤ ρ := le_of_lt hρ
    have h0 := hpos ρ hρ'
    have h1 : HasDerivAt (fun ρ : ℝ => (ρ - r0) ^ 2 + w ^ 2) (2 * (ρ - r0)) ρ := by
      have := ((hasDerivAt_id ρ).sub_const r0).pow 2
      simpa using this.add_const (w ^ 2)
    have h2 := (h1.inv h0.ne').const_mul (-(1 / 2))
    refine h2.congr_deriv ?_
    show _ = (ρ - r0) * (((ρ - r0) ^ 2 + w ^ 2)⁻¹) ^ 2
    field_simp
  have hnn : ∀ ρ ∈ Ioi r, 0 ≤ g' ρ := by
    intro ρ hρ
    have : 0 < ρ - r0 := by have : r < ρ := hρ; linarith
    simp only [hg']
    positivity
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun ρ : ℝ => (ρ - r0) ^ 2 + w ^ 2) atTop atTop := by
      refine tendsto_atTop_add_const_right _ _ ?_
      exact (tendsto_pow_atTop (two_ne_zero)).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
    have h2 := (tendsto_inv_atTop_zero.comp h1).const_mul (-(1 / 2) : ℝ)
    simpa [hg] using h2
  have hcont : ContinuousWithinAt g (Ici r) r := by
    refine ContinuousAt.continuousWithinAt ?_
    have h0 := hpos r le_rfl
    simp only [hg]
    fun_prop (disch := exact h0.ne')
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hder hnn hlim
  have hI : ∫ ρ in Ioi r, g' ρ = 0 - g r :=
    integral_Ioi_of_hasDerivAt_of_nonneg hcont hder hnn hlim
  have hle : ∀ ρ ∈ Ioi r, ρ * (((ρ - r0) ^ 2 + w ^ 2)⁻¹) ^ 2 ≤ κ * g' ρ := by
    intro ρ hρ
    have hρ' : r < ρ := hρ
    have h1 : ρ ≤ κ * (ρ - r0) := by
      rw [hκ, div_mul_eq_mul_div, le_div_iff₀ hD]
      nlinarith
    have h2 : 0 ≤ (((ρ - r0) ^ 2 + w ^ 2)⁻¹) ^ 2 := by positivity
    simp only [hg']
    calc ρ * (((ρ - r0) ^ 2 + w ^ 2)⁻¹) ^ 2 ≤ (κ * (ρ - r0)) * (((ρ - r0) ^ 2 + w ^ 2)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = κ * ((ρ - r0) * (((ρ - r0) ^ 2 + w ^ 2)⁻¹) ^ 2) := by ring
  calc ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ * (((ρ - r0) ^ 2 + w ^ 2)⁻¹) ^ 2)
      ≤ ∫⁻ ρ in Ioi r, ENNReal.ofReal (κ * g' ρ) :=
        setLIntegral_mono' measurableSet_Ioi fun ρ hρ => ENNReal.ofReal_le_ofReal (hle ρ hρ)
    _ = ENNReal.ofReal (∫ ρ in Ioi r, κ * g' ρ) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hint.const_mul κ)]
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
        exact mul_nonneg hκ0 (hnn ρ hρ)
    _ ≤ ENNReal.ofReal (w2M r0 D w) := by
        rw [integral_const_mul, hI]
        apply ENNReal.ofReal_le_ofReal
        simp only [hg, w2M, hκ]
        have h0 := hpos r le_rfl
        have h3 : (D ^ 2 + w ^ 2)⁻¹ ≥ ((r - r0) ^ 2 + w ^ 2)⁻¹ := by
          apply inv_anti₀ (by positivity)
          have : D ≤ r - r0 := by linarith
          nlinarith
        have h4 : 0 ≤ (r0 + D) / D := by positivity
        calc (r0 + D) / D * (0 - -(1 / 2) * ((r - r0) ^ 2 + w ^ 2)⁻¹)
            = (r0 + D) / D / 2 * ((r - r0) ^ 2 + w ^ 2)⁻¹ := by ring
          _ ≤ (r0 + D) / D / 2 * (D ^ 2 + w ^ 2)⁻¹ := by gcongr

theorem w2M_nonneg (r0 D w : ℝ) (hr0 : 0 ≤ r0) (hD : 0 < D) : 0 ≤ w2M r0 D w := by
  unfold w2M; positivity

theorem w2M_measurable (r0 D : ℝ) : Measurable (w2M r0 D) := by
  unfold w2M; fun_prop

theorem w2M_integrable {r0 D : ℝ} (hD : 0 < D) : Integrable (w2M r0 D) := by
  have h1 : Integrable (fun x : ℝ => (1 + (x / D) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div hD.ne'
  have h2 := h1.const_mul ((r0 + D) / D / 2 * (D ^ 2)⁻¹)
  refine h2.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [w2M]
  field_simp

end UnforcedLeray.Short.PartIIIb.Concrete
end
