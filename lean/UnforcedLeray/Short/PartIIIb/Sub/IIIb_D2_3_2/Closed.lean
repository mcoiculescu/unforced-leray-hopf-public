import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3

/-!
# `PartIII-b:IIIb-D2/3/2/12` (`WardEqClosed`): proved from the three pairing continuities

Assembles `wardEqClosed_of` (in `Sub/IIIb-D2_3_2_12.lean`) with the proved facts
`velPairCont_proved` (`IIIb-D2_3_2_12_1.lean`), `srcPairCont_proved` (`IIIb-D2_3_2_12_2.lean`)
and `strPairCont_proved` (`IIIb-D2_3_2_12_3.lean`). Source of record: lines 2683, 2698-2700,
4284-4286 of `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

theorem wardEqClosed_proved {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) (ε μ : ℝ) (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) : WardEqClosed B ε μ :=
  wardEqClosed_of B ε μ hc hν hε (velPairCont_proved c γ ν ε) (srcPairCont_proved c ε)
    (strPairCont_proved c mZ ρb γ ν ε)

end UnforcedLeray.Short.PartIIIb.Concrete
