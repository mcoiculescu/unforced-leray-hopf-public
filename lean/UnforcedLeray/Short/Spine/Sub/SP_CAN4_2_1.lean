import UnforcedLeray.Short.Spine.Sub.SP_CAN4_2

/-!
# Spine: `MildDomainDerivative` reduced to a Duhamel identity and two one-sided derivatives


Source: `the November 2 reference manuscript`, line 1086 and lines 1134-1145.

Mathematics. Let `V` be mild on `(0, ∞)`, continuous into every `X_{G,j}`, and `θ > 0` with
`V θ ∈ 𝒟(D)`. Put `g(u) = L₀ V(-u)`. For `0 < s ≤ s'` the Duhamel identity (`S_mild`,
`V(-u) = S(-u, s') V s'`) reads
`V s = e^{(log s' - log s) D} V s' + ∫_{-s'}^{-s} e^{(log(-u) - log s) D} g(u) du`.

* Left derivative (`s < θ`, take `s' = θ`): `V s - V θ = (e^{hD} - 1) V θ + J(s)` with
  `h = log θ - log s` and `J(s) = ∫_{-θ}^{-s} e^{(log(-u) - log s) D} g(u) du`. Since `V θ ∈ 𝒟(D)`,
  `(e^{hD} - 1) V θ / (s - θ) → -θ⁻¹ D V θ`, and `J(s)/(s - θ) → -g(-θ) = -L₀ V θ` by joint strong
  continuity of `(a, x) ↦ e^{aD} x` and continuity of `V` at `θ`.
* Right derivative (`s > θ`, take the identity with `(θ, s)` in place of `(s, s')`):
  `V s - V θ = -(e^{hD} - 1) V s - ∫_{-s}^{-θ} e^{(log(-u) - log θ) D} g(u) du`, `h = log s - log θ`.
  Now `(e^{hD} - 1) V s / h = h⁻¹ ∫_0^h e^{rD} D V s dr → D V θ` because `s ↦ D V s = V s - (I - D) V s`
  is continuous at `θ` (`IsXGjContinuous` at `j = 2`, `B0123.XGj_two`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- **Duhamel identity for a mild `V`** (shorter proof lines 1134-1145; `S_mild`,
`Cons/L2/CanonicalBranch/Evolution.lean:232`, with `V(-u) = S(-u, θ'') V θ''` on `[θ, θ'']`):
`V θ = e^{(log θ'' - log θ) D} V θ'' + ∫_{-θ''}^{-θ} e^{(log(-u) - log θ) D} L₀ V(-u) du`
for `0 < θ ≤ θ''`. -/
def MDDuhamel : Prop :=
  ∀ V : ℝ → XG, IsMildOnPos V → ∀ θ θ'' : ℝ, 0 < θ → θ ≤ θ'' →
    V θ = B0123.expD (Real.log θ'' - Real.log θ) (V θ'') +
      ∫ u in (-θ'')..(-θ), B0123.expD (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u)))

/-- **Left derivative** (shorter proof lines 1134-1145): `V` has the one-sided derivative
`-(L₀ V θ + θ⁻¹ D V θ)` from the left at `θ > 0` with `V θ ∈ 𝒟(D)`. Uses `s' = θ` in the Duhamel
identity; see the module docstring. -/
def MDLeft : Prop :=
  GreenAll → ∀ V : ℝ → XG, IsMildOnPos V → IsXGjContinuous V →
    ∀ θ : ℝ, 0 < θ → ∀ h : V θ ∈ B0094.D.domain,
      HasDerivWithinAt V (-(B0012.L0 (V θ) + ((θ : ℂ)⁻¹) • B0094.D ⟨V θ, h⟩)) (Iic θ) θ

/-- **Right derivative** (shorter proof lines 1134-1145): the same one-sided derivative from the
right. Needs continuity of `s ↦ D V s` at `θ` (`IsXGjContinuous` at `j = 2`). -/
def MDRight : Prop :=
  GreenAll → ∀ V : ℝ → XG, IsMildOnPos V → IsXGjContinuous V →
    ∀ θ : ℝ, 0 < θ → ∀ h : V θ ∈ B0094.D.domain,
      HasDerivWithinAt V (-(B0012.L0 (V θ) + ((θ : ℂ)⁻¹) • B0094.D ⟨V θ, h⟩)) (Ici θ) θ

/-- Two one-sided derivatives give the derivative. -/
theorem mildDomainDerivative_of (hL : MDLeft) (hR : MDRight) : MildDomainDerivative := by
  intro hE V hV hC θ hθ h
  have := (hL hE V hV hC θ hθ h).union (hR hE V hV hC θ hθ h)
  rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
  exact this

end UnforcedLeray.Short.Spine
