import UnforcedLeray.Short.PartIIIa.Sub.T18_2

/-!
# Part III-a, shared leaf statement of `T18/2/1` and `T18/2/3`: the triangle inequality for `𝒯`

Both `CausalLimitAE` (`Sub/T18_2_1.lean`) and `NiceForceApprox` (`Sub/T18_2_3.lean`) need the
triangle inequality for the gain-conjugated `𝒯` norm (`tCalNorm c (gainConj γ ν ·)`), in the
orientation "`(X - Z) ≤ (X - Y) + (Z - Y)`" (all three differences are of the form
"approximant minus limit").
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Triangle inequality for the gain-conjugated `𝒯` norm** (`PartIII-a:T18/2/1/1`; used in
`T18/2/1` and `T18/2/3`; SP 3427-3440). For measurable tensor fields `X, Y, Z`,
`‖g⁻¹(X - Z)‖_𝒯 ≤ ‖g⁻¹(X - Y)‖_𝒯 + ‖g⁻¹(Z - Y)‖_𝒯`. Proof: pointwise
`tnorm2 (g⁻¹(X-Z)) ≤ tnorm2 (g⁻¹(X-Y)) + tnorm2 (g⁻¹(Z-Y))` (Frobenius norm, `gainConj` is a real
scalar multiple), `eLpNorm_mono_ae` and `eLpNorm_add_le` (measurability of the norms from
`causalLin_measurable_tnorm2` in `T18_FreeCausal/Lin.lean`). No hypothesis on `c, ν, γ`. -/
def TCalNormTriangle : Prop :=
  ∀ (c ν γ : ℝ) (X Y Z : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    (∀ i j, Measurable fun p => X p i j) → (∀ i j, Measurable fun p => Y p i j) →
    (∀ i j, Measurable fun p => Z p i j) →
    tCalNorm c (gainConj γ ν (fun p i j => X p i j - Z p i j)) ≤
      tCalNorm c (gainConj γ ν (fun p i j => X p i j - Y p i j)) +
        tCalNorm c (gainConj γ ν (fun p i j => Z p i j - Y p i j))

end UnforcedLeray.Short.IIIa
