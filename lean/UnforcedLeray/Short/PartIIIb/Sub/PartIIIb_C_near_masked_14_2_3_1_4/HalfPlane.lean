import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1_4.Assembly

/-!
# `HalfPlaneToSpace` from polar coordinates and a one-dimensional substitution
(`PartIII-b:C/near/masked/14/2/3/1/4`; source 2683, 3996-4011)

Source: `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst

/-- **Polar coordinates in the first two coordinates of `ℝ³`** (source 3996-4011): for measurable
axisymmetric `H` (a function of `(y₀²+y₁², y₂)`),
`∫_{ℝ³} H = 2π ∫_{ρ>0}∫_{z∈ℝ} ρ H(ρ, 0, z) dz dρ`.
(Mathlib `lintegral_comp_polarCoord_symm` in `(y₀,y₁)` and Fubini across the splitting
`Space ≃ᵐ (ℝ × ℝ) × ℝ`; the angle integral is `2π` by axisymmetry.) -/
def SpacePolar : Prop :=
  ∀ H : Space → ℝ≥0∞, Measurable H →
    (∀ y y' : Space, y 0 ^ 2 + y 1 ^ 2 = y' 0 ^ 2 + y' 1 ^ 2 → y 2 = y' 2 → H y = H y') →
      ∫⁻ y : Space, H y = ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ z : ℝ, ENNReal.ofReal ρ * H (WithLp.toLp 2 ![ρ, 0, z])

/-- **Self-similar substitution** (source 2683): for measurable `F : ℝ → ℝ → ℝ≥0∞` and `R > 0`,
`∫_{s>0}∫_η s^{-5/2} F(R/√s, η/√s) dη ds = (2/R²) ∫_{ρ>0}∫_z ρ F(ρ, z) dz dρ`
(`ρ = R/√s`, `z = η/√s`: `dη = √s dz`, `s^{-5/2} ds = (2/R²) ρ · s^{1/2}… dρ`, i.e. the one
dimensional substitutions `η = √s z` then `s = R²/ρ²`). -/
def SlicesChange : Prop :=
  ∀ R : ℝ, 0 < R → ∀ F : ℝ → ℝ → ℝ≥0∞, Measurable (Function.uncurry F) →
    ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η : ℝ,
        ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * F (R / Real.sqrt s) (η / Real.sqrt s) =
      ENNReal.ofReal (2 / R ^ 2) *
        ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ z : ℝ, ENNReal.ofReal ρ * F ρ z

theorem halfPlaneToSpace_of (h1 : SpacePolar) (h2 : SlicesChange) : HalfPlaneToSpace := by
  intro R hR H hH hax
  have hF : Measurable (Function.uncurry fun ρ z : ℝ => H (WithLp.toLp 2 ![ρ, 0, z])) := by
    refine hH.comp ?_
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp ?_
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  have e1 := h2 R hR (fun ρ z => H (WithLp.toLp 2 ![ρ, 0, z])) hF
  have e2 := h1 H hH hax
  have e3 : ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η : ℝ,
        ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * H (chartY R (s, (0, η))) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) *
        H (WithLp.toLp 2 ![R / Real.sqrt s, 0, η / Real.sqrt s]) := rfl
  rw [e3, e1, e2, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
