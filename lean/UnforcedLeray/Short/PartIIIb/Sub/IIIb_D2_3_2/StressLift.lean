import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLiftDefs
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift.VelYH
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift.CartLift
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift.StrSumAE
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift.VelAdd

/-!
# `WardStressLift` assembled from its four lemmas (source 4147, 4161-4174)

The target `wardStressLift_proved` is `wardStressLift_of` applied to the four proved lemmas:
`wardVelPhysYH_proved` (VelYH), `cartLiftSymOuter_proved` (CartLift), `strSumExactAE_proved`
(StrSumAE) and `velAddAE_proved` (VelAdd).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

section StressLiftProved

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

theorem wardStressLift_proved {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) (hc : 0 < c)
    (hρb : 0 < ρb) {ε : ℝ} (hε : 0 < ε) (hν : 0 < ν) {μ : ℝ} {χo : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ) (V rb : ℝ → SpatialField)
    (p : ℝ → Space → ℝ) : WardStressLift B hc ε hε hν μ hχo χy V rb p :=
  wardStressLift_of B hc hρb hε hν hχo χy V rb p (wardVelPhysYH_proved B hc hε hν μ hχo χy _ p)
    (cartLiftSymOuter_proved _ _ _) (strSumExactAE_proved B hc hρb ε V rb) (velAddAE_proved c γ ν)

end StressLiftProved

end UnforcedLeray.Short.PartIIIb.Concrete
