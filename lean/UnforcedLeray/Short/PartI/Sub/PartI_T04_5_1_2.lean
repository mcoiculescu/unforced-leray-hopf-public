import UnforcedLeray.Short.PartI.Sub.PartI_T04_5_1

/-!
# Decomposition of `apEnergyHasDeriv` (`PartI:T04/5/1/2`, source 278-286)

Source `the November 2 reference manuscript`
278-286.  `F_R'(s) = ∫ χ_R · 2⟨v, ∂_s v⟩` (differentiation under the integral sign, a copy of
`ccEH_generic` with `W = v`), and the momentum equation turns the integral into `apEnergyRhs`
(viscous, transport and pressure identities, single-solution analogues of `CcIntegrandDecomp`,
`CcViscousIdentity`, `CcTransportIdentity`, `CcPressureIdentity` of `Sub/T02_3_11.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Differentiation under the integral sign: `F_R' = ∫_cell χ_R · 2⟨v, ∂_s v⟩` on `(0,T)`
(copy of `ccEH_generic`, `Tasks/ClassicalOdd/ClassicalCutoffEnergyIneq/HasDeriv.lean` 132-213,
with `W = v`; smoothness from `IsAPrioriClass`). -/
def APEnergyDerivIntegral : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      HasDerivAt (apCutoffEnergy c v R)
        (∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * inner ℝ (v s z) (deriv (fun t => v t z) s))) s

/-- Momentum identity: with `∂_s v = -(v·∇)v + νΔv - ∇p` (`hcls.classical.momentum`), `div v = 0`,
periodicity in `q` and compact `η`-support of `χ_R`,
`∫ χ_R 2⟨v,∂_s v⟩ = apEnergyRhs` (viscous, transport, pressure integrations by parts). -/
def APEnergyMomentumIdentity : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      (∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * inner ℝ (v s z) (deriv (fun t => v t z) s))) =
        apEnergyRhs ν c v p R s

theorem apEnergyHasDeriv_of (h1 : APEnergyDerivIntegral) (h2 : APEnergyMomentumIdentity) :
    APEnergyHasDeriv := by
  intro ν c T v p hν hc hcls R hR s hs
  have := h1 ν c T v p hν hc hcls R hR s hs
  rwa [h2 ν c T v p hν hc hcls R hR s hs] at this

end UnforcedLeray.Short.PartI
