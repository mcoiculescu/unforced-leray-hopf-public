import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_9.RhoW1Of
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularityProof

/-!
# `PartIII-b:C/rep/9/2`: `δ_U ≤ P_ν ρ` for large `n`, from `short-bg:strong`

Source `the November 2 reference manuscript` 5094 ("`δ_U ≤ P_νρ` from the
background bounds"), 5007-5008 (`δ_U = ‖U - U_raw‖_{W^{1,∞}}`), 2538-2541 (`short-bg:strong`).

Discharges `D.RhoW1` unconditionally under `D.RepairStanding dm dp` via `rhoW1_of`,
`bgW1Levels_of'`, and `UnforcedLeray.Short.IIb.strongRegularity_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`δ_U ≤ P_ν ρ` for large `n` from `short-bg:strong`** (source 5094, 5007-5008, 2538-2541):
the repair standing and `IIb.StrongRegularity` give `RhoW1`, through `BgW1Levels`
(`bgW1Levels_of'`). -/
theorem repairStanding_rhoW1_of_strongRegularity (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) (hSR : UnforcedLeray.Short.IIb.StrongRegularity) :
    D.RhoW1 :=
  rhoW1_of D hst (bgW1Levels_of' hSR)

/-- **`δ_U ≤ P_ν ρ` for large `n`** (source 5094, 5007-5008, 2538-2541): unconditional `RhoW1`
from `RepairStanding` and `IIb.strongRegularity_proof`. -/
theorem repairStanding_rhoW1 (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.RhoW1 :=
  rhoW1_of D hst (bgW1Levels_of' UnforcedLeray.Short.IIb.strongRegularity_proof)

end UnforcedLeray.Short.PartIIIb.Concrete

#print axioms UnforcedLeray.Short.PartIIIb.Concrete.repairStanding_rhoW1
