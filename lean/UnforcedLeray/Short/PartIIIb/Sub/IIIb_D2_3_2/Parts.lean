import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Defs

/-!
# Assembly of `wardHEquation_of` from its parts (source 4225-4286)

See `Defs.lean`.  `wardHEquation_of_parts` combines the pointwise identity (1), the weak form for
smooth inputs (3), density (4a) and continuity (4b).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

theorem wardHEquation_of_parts (B : ReturnBase c mZ ρb γ ν Aff) {ε μ : ℝ} {χo χy : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) {V rb : ℝ → SpatialField} {p : ℝ → Space → ℝ}
    (hUp : IsExactProfile ν (2 * ε * c) (fun τ y => V τ y + rb τ y) p)
    (hM : IsExactMultiplier B ε⁻¹ V rb)
    (hax : ∀ τ, AxiNoSwirlPt (fun y => V τ y + rb τ y))
    (hW : IsWardPinned B ε μ hχo χy (fun τ y => V τ y + rb τ y) p)
    (h1 : WardPointwiseIdentity ν μ (fun τ y => V τ y + rb τ y) p)
    (h3 : WardWeakFromPointwise B ε μ hχo χy V rb p)
    (h4a : WardSmoothDense B ε μ hχo χy (fun τ y => V τ y + rb τ y) p)
    (h4b : WardEqClosed B ε μ) : WardHEquation B ε μ :=
  wardHEquation_of_dense_closed B h4a h4b (h3 h1 hUp hM hax hW)

end UnforcedLeray.Short.PartIIIb.Concrete
