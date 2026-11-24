import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1_b
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_4
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree

/-!


The chart coefficient of `wardH` is measurable.  The old source representatives `g₁, g₂` are
replaced by measurable representatives `g₁', g₂'` (`AEStronglyMeasurable.ae_eq_mk`), which agree
with `g₁ + g₂` on the `ageμ c (-1/2)` class (`NearInst.ae_gainZ1Measure`,
`NearInst.ae_z1Measure`, `NearInst.ae_gainHTMeasure`, `NearInst.ae_htRhoMeasure`).  Then
`wardX0_congr_ae` (`T8_1_b`) gives the same `wardX0`, hence the same `wardX`, `wardH` and
`WardXRegularAt`, and `coefOf_wardH_measurable` (`T8_4`) finishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem wardHCoefMeasurable_of (c mZ ρb γ ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (χy : ℝ → ℝ) (U : ℝ → SpatialField) (hreg : WardXRegular c mZ ρb γ ν ε μ hχo χy) :
    WardHCoefMeasurable c mZ ρb γ ν ε μ hχo χy U := by
  unfold WardHCoefMeasurable
  intro hχy hU hUm hc hρ hm hν hε hμ T g₁ g₂ h1 h2
  have hr := hreg hχy hc hρ hm hν hε hμ T g₁ g₂ h1 h2
  have hm1 : AEStronglyMeasurable g₁ (gainZ1Measure c mZ γ ν) :=
    (Lp.aestronglyMeasurable ((chiOStr c mZ ρb γ ν hχo T).fst)).congr h1
  have hm2 : AEStronglyMeasurable g₂ (gainHTMeasure c ρb γ ν) :=
    (Lp.aestronglyMeasurable ((chiOStr c mZ ρb γ ν hχo T).snd)).congr h2
  obtain ⟨g₁', e1, hmeas1⟩ : ∃ g', g₁ =ᵐ[gainZ1Measure c mZ γ ν] g' ∧ Measurable g' :=
    ⟨hm1.mk g₁, hm1.ae_eq_mk, hm1.stronglyMeasurable_mk.measurable⟩
  obtain ⟨g₂', e2, hmeas2⟩ : ∃ g', g₂ =ᵐ[gainHTMeasure c ρb γ ν] g' ∧ Measurable g' :=
    ⟨hm2.mk g₂, hm2.ae_eq_mk, hm2.stronglyMeasurable_mk.measurable⟩
  have a1 : ∀ᵐ p ∂(ageμ c (-1 / 2)), g₁ p = g₁' p := by
    have h := e1
    rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at h
    exact h
  have a2 : ∀ᵐ p ∂(ageμ c (-1 / 2)), g₂ p = g₂' p := by
    have h := e2
    rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at h
    exact h
  have hsum : ∀ᵐ p ∂(ageμ c (-1 / 2)), (g₁ + g₂) p = (g₁' + g₂') p := by
    filter_upwards [a1, a2] with p hp1 hp2
    simp only [Pi.add_apply, hp1, hp2]
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.mpr hε
  have hX0 := wardX0_congr_ae ν μ ε⁻¹ c hR hc (g₁ + g₂) (g₁' + g₂') hsum
  have hWX : wardX ν μ ε⁻¹ c χy (g₁ + g₂) = wardX ν μ ε⁻¹ c χy (g₁' + g₂') := by
    unfold wardX
    rw [hX0]
  have hWH : wardH ν μ ε⁻¹ c χy U (g₁ + g₂) = wardH ν μ ε⁻¹ c χy U (g₁' + g₂') := by
    funext τ y
    simp only [wardH, hWX]
  have hr' : WardXRegularAt ν μ ε⁻¹ c χy (g₁' + g₂') := by
    unfold WardXRegularAt at hr ⊢
    obtain ⟨X, hX1, hX2, hX3, hX4, hX5⟩ := hr
    exact ⟨X, hX1, fun τ y hy => (hX2 τ y hy).trans (congrFun (congrFun hWX τ) y),
      hX3, hX4, hX5⟩
  have hg : Measurable (g₁' + g₂') := hmeas1.add hmeas2
  rw [hWH]
  exact coefOf_wardH_measurable hR hχy hU hUm hg hr'

end UnforcedLeray.Short.PartIIIb.Concrete
