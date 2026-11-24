import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Parts
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Ward3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.IBPLoc
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Pointwise
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Lifts
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Closed

/-!
# `wardHEquation_of` (source 4225-4286)

Source: `the November 2 reference manuscript`.
Assembly of the weak Ward equation from `/7`, `/9`, `/10`, `/11`, `/12` and `wardIBPLoc_proved`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem wardHEquation_of {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) {ε μ : ℝ} {χo χy : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (hχy : IsYoungCutoff χy) {V rb : ℝ → SpatialField} {p : ℝ → Space → ℝ} (hc : 0 < c) (hρb : 0 < ρb) (hν : 0 < ν) (hε : 0 < ε) (hμ0 : 0 < μ) (hμ1 : μ < 1 / 4) (hUp : IsExactProfile ν (2 * ε * c) (fun τ y => V τ y + rb τ y) p) (hM : IsExactMultiplier B ε⁻¹ V rb) (hax : ∀ τ, AxiNoSwirlPt (fun y => V τ y + rb τ y)) (hW : IsWardPinned B ε μ hχo χy (fun τ y => V τ y + rb τ y) p) : WardHEquation B ε μ :=
  wardHEquation_of_parts B hχo hUp hM hax hW (wardPointwiseIdentity_proved ν μ _ p)
    (wardWeakFromPointwise_of_parts B hc hε hν hχo
      (wardIBPLoc_proved ν μ _ (mul_pos (mul_pos two_pos hε) hc))
      (wardLifts_proved B hc hε hν hχo χy _ p)
      (wardStressLift_proved B hc hρb hε hν hχo χy V rb p))
    (wardSmoothDense_proved B hχo χy hχy hc hν hε (by linarith) hUp hax)
    (wardEqClosed_proved B ε μ hc hν hε)

end UnforcedLeray.Short.PartIIIb.Concrete
