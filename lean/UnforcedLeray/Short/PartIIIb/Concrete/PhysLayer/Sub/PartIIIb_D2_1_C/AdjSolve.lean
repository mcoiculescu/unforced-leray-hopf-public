import UnforcedLeray.Short.PartIIb.Bridge.Adjoint
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint
import UnforcedLeray.Short.PartIIb.Bridge.Tasks.AdjSolSolenoidal
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1

/-!
# `PartIII-b:IIIb-D2/1/3/1/1`: `fwuAdjSolve`

Source `the November 2 reference manuscript` lines 1351-1362.
The statement is the bridge lemma `field_adjoint_exists_of` applied to the common-body adjoint
(`PartII-a:F09`) and the adjoint solenoidality (`PartII-b:T10/org/3`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fwuAdjSolve : FWUAdjSolve := by
  intro P ν μ hP hP1 hν hμ f hf hs
  exact UnforcedLeray.Short.IIb.field_adjoint_exists_of
    UnforcedLeray.Short.PartIIa.commonBodyAdjoint
    UnforcedLeray.Short.IIb.adjSolSolenoidal P ν μ hP hP1 hν hμ f hf hs

end UnforcedLeray.Short.PartIIIb.Concrete
