import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_3

/-!
# `PartIII-b:IIIb-D2/3`: `wardEnergyEquation_of`

Source: `the November 2 reference manuscript`,
lines 4260-4303 (Ward energy equation), with the background axisymmetry at 121-124 and 4144-4145.

Assembly of the three leaves: `WeakDmuAdd` (`weakDmuAdd_proved`), the solenoidality of the Ward
field `h` (`wardHSolenoidal_of`) and its weak equation (`wardHEquation_of`), fed into the
abstract energy-equation lemma `wardEnergyEquation_of_parts` of `Sub/PartIIIb-D2_3.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem wardEnergyEquation_of {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) {ε μ : ℝ} {χo χy : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (hχy : IsYoungCutoff χy) {V rb : ℝ → SpatialField} {p : ℝ → Space → ℝ} (hc : 0 < c) (hρb : 0 < ρb) (hmZ : 0 ≤ mZ) (hν : 0 < ν) (hε : 0 < ε) (hμ0 : 0 < μ) (hμ1 : μ < 1 / 4) (hUp : IsExactProfile ν (2 * ε * c) (fun τ y => V τ y + rb τ y) p) (hM : IsExactMultiplier B ε⁻¹ V rb) (hax : ∀ τ, AxiNoSwirlPt (fun y => V τ y + rb τ y)) (hS : IsStressInverse B ε μ) (hW : IsWardPinned B ε μ hχo χy (fun τ y => V τ y + rb τ y) p) : WardEnergyEquation B ε μ :=
  wardEnergyEquation_of_parts B (weakDmuAdd_proved c γ ν ε μ hc hν hε) hS
    (wardHSolenoidal_of B hχo hχy hc hρb hmZ hν hε hμ0 hUp hax hW)
    (wardHEquation_of B hχo hχy hc hρb hν hε hμ0 hμ1 hUp hM hax hW)

end UnforcedLeray.Short.PartIIIb.Concrete
