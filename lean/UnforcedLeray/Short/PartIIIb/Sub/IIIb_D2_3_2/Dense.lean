import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Defs
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.StrDense
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.XSmooth
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.FieldsSmooth
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.FieldsAxi
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.AxiLift

/-!
# `PartIII-b:IIIb-D2/3/2/11` (`wardSmoothDense_proved`)

Source: `the November 2 reference manuscript`
4284-4286, 4161-4186, 3604-3621, 121-124.

The density of the smooth Ward class, assembled from the five proved leaves
`strSmoothDense_proved` (`/11/1`), `wardXrSmoothData_proved` (`/11/2`),
`wardFieldsSmooth_proved` (`/11/3`), `wardFieldsAxi_proved` (`/11/4`) and
`axiLiftOfAxi_proved` (`/11/5`) through `wardSmoothDense_of` (`Dense/Defs.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `PartIII-b:IIIb-D2/3/2/11` target: the smooth Ward class is dense. -/
theorem wardSmoothDense_proved {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) {ε μ : ℝ}
    {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ) (hχy : IsYoungCutoff χy)
    {U : ℝ → SpatialField} {p : ℝ → Space → ℝ} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε)
    (hμ : -(1 / 4) < μ) (hUp : IsExactProfile ν (2 * ε * c) U p)
    (hax : ∀ τ, AxiNoSwirlPt (U τ)) : WardSmoothDense B ε μ hχo χy U p :=
  wardSmoothDense_of B hχo χy hχy hc hν hε hμ hUp hax (strSmoothDense_proved c mZ ρb γ ν)
    wardXrSmoothData_proved wardFieldsSmooth_proved wardFieldsAxi_proved axiLiftOfAxi_proved

end UnforcedLeray.Short.PartIIIb.Concrete
