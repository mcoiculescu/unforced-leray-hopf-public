import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_3

/-!
# `RepsVecEquation` decomposed (task `PartIII-b:C/near/pins/3/4`)

Source `the November 2 reference manuscript`:
1675-1677 (`R_ε^vec(μ) = (μ - A_ε)⁻¹`), 1339-1362 (free Cartesian equation `L = 𝒯 - νΔ - 1/2`),
4139-4146 (`D_μ = L₀ + μ`).

Reuses `PairFunctional` (task `.../3/3`).  Leaves: the dual test `D_μᵗΦ = L₀ᵗΦ + μΦ` also has a
bounded pairing functional (`PairFunctionalDual`), and the weak generator identity
`ℓ_{D_μᵗΦ}(u) = ℓ_Φ((μ - A_ε)u)` on the graph of the outer generator (`GenAdjointPair`: integration
by parts for `ν ε² Δ_x + x·∇/2 + 1/2 - ∂_τ` on outer variables against smooth periodic tests,
transported `y = x/ε` through the `liftVec` ↔ `velPhys` dictionary).  The resolvent step
(`B0223.RepsVec_right`) is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- **Leaf 1**: the dual test `D_μᵗΦ = L₀ᵗΦ + μΦ` of a solenoidal phase test has a bounded pairing
functional on `H` (source 4139-4146; same dictionary as `PairFunctional`, the dual test is again
smooth, periodic and decaying). -/
def PairFunctionalDual : Prop :=
  ∀ (p : Params) (μ : ℝ) (Φ : ℝ × Space → CVec3), IsSolTest (2 * p.ε * p.c) Φ →
    ∃ ℓ : HSpace p.c MeridC →L[ℂ] ℂ, ∀ (g : HSpace p.c MeridC) (f : Chart → Merid),
      ChartRep p.c g f → ℓ g = pairF (2 * p.ε * p.c) (fun x => L0T p.ν Φ x + (μ : ℂ) • Φ x)
        (velPhys p.ε⁻¹ p.c f)

/-- **Leaf 2 (weak generator identity)** (source 1339-1362, 4139-4146; `B0223.J_RepsVec`,
`RepsVec_right`): if `(lift u, lift Au)` is in the graph of the outer semigroup generator, then
`ℓ_{D_μᵗΦ}(u) = ℓ_Φ(μ u - A u)`, for the pairing functionals of `D_μᵗΦ` and `Φ`. -/
def GenAdjointPair : Prop :=
  ∀ (p : Params) (μ : ℝ) (Φ : ℝ × Space → CVec3), IsSolTest (2 * p.ε * p.c) Φ →
    ∀ (ℓΦ ℓD : HSpace p.c MeridC →L[ℂ] ℂ),
      (∀ (g : HSpace p.c MeridC) (f : Chart → Merid), ChartRep p.c g f →
        ℓΦ g = pairF (2 * p.ε * p.c) Φ (velPhys p.ε⁻¹ p.c f)) →
      (∀ (g : HSpace p.c MeridC) (f : Chart → Merid), ChartRep p.c g f →
        ℓD g = pairF (2 * p.ε * p.c) (fun x => L0T p.ν Φ x + (μ : ℂ) • Φ x)
          (velPhys p.ε⁻¹ p.c f)) →
      ∀ u Au : HSpace p.c MeridC,
        UnforcedLeray.B0223.IsGenPair
          (UnforcedLeray.B0223.outerS (E := UnforcedLeray.B0223.SpaceC) (P := p.period) p.ν_pos p.ε)
          (UnforcedLeray.B0223.liftVec (P := p.period) p.ε_pos p.c_pos rfl u)
          (UnforcedLeray.B0223.liftVec (P := p.period) p.ε_pos p.c_pos rfl Au) →
        ℓD u = ℓΦ ((μ : ℂ) • u - Au)

theorem repsVecEquation_of (h1 : PairFunctional) (h2 : PairFunctionalDual)
    (h3 : GenAdjointPair) : RepsVecEquation := by
  intro p μ hP hμ γ z wz w hz hw Φ hΦ
  obtain ⟨ℓΦ, hΦ'⟩ := h1 p.c p.ε p.c_pos p.ε_pos Φ hΦ
  obtain ⟨ℓD, hD'⟩ := h2 p μ Φ hΦ
  have hγ : 0 < ((μ : ℂ)).re + 1 / 4 := by simp; linarith
  have hgen := UnforcedLeray.B0223.RepsVec_right (P := p.period) p.ν_pos p.ε_pos
    p.c_pos rfl hγ z
  have key := h3 p μ Φ hΦ ℓΦ ℓD hΦ' hD' _ _ hgen
  rw [← hD' _ _ hw, ← hΦ' _ _ hz, key]
  simp

end UnforcedLeray.Short.PartIIIb.NearInst
