import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Defs

/-!
# From the raw to the regularized Ward fields (source 4161-4186)

Source: `the November 2 reference manuscript`.

`SmoothWardInput` (`Defs.lean`) states its smoothness and lift fields for the regularized Ward
fields of `Dense/Reg.lean`, while `IsWardPinned` and the statements of `WardLifts`,
`WardStressLift`, `WardVelPhysYH` are written with the raw fields.  The two differ only on the
axis (`ℝ × axis` is null), and the chart coefficients agree.  This file packages that:

* `wardPinned_reg`: the pins of `IsWardPinned` with the regularized fields;
* `ae_snd_not_mem_axis`, `ae_eq_of_offAxis'`: off-axis agreement is `volume`-a.e. agreement on
  `ℝ × ℝ³`;
* `realC_wardHr_ae`, `realC_wardEr_ae`, `realC_wardYHr_ae`: the complexified fields agree a.e.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `ℝ × axis` is a null set of `ℝ × ℝ³`. -/
theorem ae_snd_not_mem_axis : ∀ᵐ x : ℝ × Space ∂(volume : Measure (ℝ × Space)), x.2 ∉ axis := by
  have h : (volume : Measure (ℝ × Space)) (Prod.snd ⁻¹' axis) = 0 := by
    rw [show (Prod.snd ⁻¹' axis : Set (ℝ × Space)) = univ ×ˢ axis by ext x; simp,
      Measure.volume_eq_prod, Measure.prod_prod, volume_axis, mul_zero]
  exact measure_eq_zero_iff_ae_notMem.1 h

/-- Fields on `ℝ × ℝ³` that agree off the axis agree `volume`-a.e. -/
theorem ae_eq_of_offAxis' {E : Type*} {F G : ℝ → Space → E}
    (h : ∀ τ y, y ∉ axis → F τ y = G τ y) :
    (fun x : ℝ × Space => F x.1 x.2) =ᵐ[volume] fun x => G x.1 x.2 := by
  filter_upwards [ae_snd_not_mem_axis] with x hx
  exact h x.1 x.2 hx

section Fields

variable (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ)
  (g : Chart → Ten3)

theorem realC_wardHr_ae :
    (fun x : ℝ × Space => B0412.realC (wardHr ν μ R c χy U g x.1 x.2)) =ᵐ[volume]
      fun x => B0412.realC (wardH ν μ R c χy U g x.1 x.2) :=
  ae_eq_of_offAxis' (F := fun τ y => B0412.realC (wardHr ν μ R c χy U g τ y))
    (G := fun τ y => B0412.realC (wardH ν μ R c χy U g τ y)) fun τ _ hy => by
      simp only [wardHr_eq_of_not_mem ν μ R c χy g U τ hy]

theorem realC_wardEr_ae :
    (fun x : ℝ × Space => B0412.realC (wardEr ν μ R c χy U p g x.1 x.2)) =ᵐ[volume]
      fun x => B0412.realC (wardE ν μ R c χy U p g x.1 x.2) :=
  ae_eq_of_offAxis' (F := fun τ y => B0412.realC (wardEr ν μ R c χy U p g τ y))
    (G := fun τ y => B0412.realC (wardE ν μ R c χy U p g τ y)) fun τ _ hy => by
      simp only [wardEr_eq_of_not_mem ν μ R c χy g U p τ hy]

theorem realC_wardYHr_ae :
    (fun x : ℝ × Space => B0412.realC (wardYr ν μ R c χy g x.1 x.2 +
        wardHr ν μ R c χy U g x.1 x.2)) =ᵐ[volume]
      fun x => B0412.realC (wardY ν μ R c χy g x.1 x.2 + wardH ν μ R c χy U g x.1 x.2) :=
  ae_eq_of_offAxis'
    (F := fun τ y => B0412.realC (wardYr ν μ R c χy g τ y + wardHr ν μ R c χy U g τ y))
    (G := fun τ y => B0412.realC (wardY ν μ R c χy g τ y + wardH ν μ R c χy U g τ y))
    fun τ _ hy => by
      simp only [wardYr_eq_of_not_mem ν μ R c χy g τ hy, wardHr_eq_of_not_mem ν μ R c χy g U τ hy]

end Fields

section Pins

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

/-- The pins of `IsWardPinned` with the regularized Ward fields (`ε ≠ 0`: the chart coefficients
of the raw and the regularized fields coincide, `coefOf_congr_offAxis`). -/
theorem wardPinned_reg (B : ReturnBase c mZ ρb γ ν Aff) {ε μ : ℝ} (hε : ε ≠ 0) {χo : ℝ → ℝ}
    {hχo : IsOutwardCutoff χo} {χy : ℝ → ℝ} {U : ℝ → SpatialField} {p : ℝ → Space → ℝ}
    (hW : IsWardPinned B ε μ hχo χy U p) (T : StrG c mZ ρb γ ν) (g₁ g₂ : Chart → Ten3)
    (h1 : ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁)
    (h2 : ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂) :
    (B.Yf T : Chart → Merid) =ᵐ[bodyMeasure c γ ν]
        coefOf ε⁻¹ (wardYr ν μ ε⁻¹ c χy (g₁ + g₂)) ∧
      (B.hf T : Chart → Merid) =ᵐ[bodyMeasure c γ ν]
        coefOf ε⁻¹ (wardHr ν μ ε⁻¹ c χy U (g₁ + g₂)) ∧
      (B.Ef T : Chart → Merid) =ᵐ[srcMeasure c]
        coefOf ε⁻¹ (wardEr ν μ ε⁻¹ c χy U p (g₁ + g₂)) := by
  have hR : ε⁻¹ ≠ 0 := inv_ne_zero hε
  obtain ⟨hY, hH, hE⟩ := hW T g₁ g₂ h1 h2
  rw [coefOf_wardY_reg χy (g₁ + g₂) hR] at hY
  rw [coefOf_wardH_reg χy U (g₁ + g₂) hR] at hH
  rw [coefOf_wardE_reg χy U p (g₁ + g₂) hR] at hE
  exact ⟨hY, hH, hE⟩

end Pins

end UnforcedLeray.Short.PartIIIb.Concrete
