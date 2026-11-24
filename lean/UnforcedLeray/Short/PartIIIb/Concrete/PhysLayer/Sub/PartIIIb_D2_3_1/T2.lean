import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.IntAll
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.IntCong
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `wardX0Structure_of` (PartIII-b:IIIb-D2/3/1/2), unconditional

Composition of the Sub theorem `UnforcedLeray.Short.PartIIIb.Concrete.wardX0Structure_of`
(`Sub/IIIb-D2_3_1_2.lean`) with its hypotheses discharged by the unconditional leaves:
`oldSourceReg_all`, `sepWSmoothOn_of` (with the kernel bounds `IIIa.sepKernelBounds`),
`sepWDivFree_all`, `oldPhysPeriodic`, `wardX0Axi_all`, `sepIntegrableOfSource_all`,
`sepIntegrableCongrAE`.

The name `wardX0Structure_of` is already taken in `UnforcedLeray.Short.PartIIIb.Concrete` by the
imported Sub theorem, so the statement is declared in `UnforcedLeray.Short.PartIIIb.Concrete.Final`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.Final

theorem wardX0Structure_of (c mZ ρb γ ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) :
    WardX0Structure c mZ ρb γ ν ε μ hχo :=
  UnforcedLeray.Short.PartIIIb.Concrete.wardX0Structure_of c mZ ρb γ ν ε μ hχo
    (UnforcedLeray.Short.PartIIIb.Concrete.oldSourceReg_all c mZ ρb γ ν ε hχo)
    (UnforcedLeray.Short.PartIIIb.Concrete.sepWSmoothOn_of UnforcedLeray.Short.IIIa.sepKernelBounds)
    UnforcedLeray.Short.PartIIIb.Concrete.sepWDivFree_all
    UnforcedLeray.Short.PartIIIb.Concrete.oldPhysPeriodic
    UnforcedLeray.Short.PartIIIb.Concrete.wardX0Axi_all
    UnforcedLeray.Short.PartIIIb.Concrete.sepIntegrableOfSource_all
    UnforcedLeray.Short.PartIIIb.Concrete.sepIntegrableCongrAE

end UnforcedLeray.Short.PartIIIb.Concrete.Final
