import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_9
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_9_1

/-!
# `WardLifts` (source 4161-4174), proved from its third clause

`wardLifts_of` reduces `WardLifts` to `WardVelPhysYH`, and `wardVelPhysYH_proved` supplies
that clause. This file only composes the two.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

theorem wardLifts_proved {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) (hν : 0 < ν) {μ : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) : WardLifts B hc ε hε hν μ hχo χy U p :=
  wardLifts_of B hc hε hν hχo χy U p (wardVelPhysYH_proved B hc hε hν hχo χy U p)

end UnforcedLeray.Short.PartIIIb.Concrete
