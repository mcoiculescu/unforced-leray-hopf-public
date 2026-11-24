import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.MassGaugeOrg

/-!
# `PartIII-b:C/rep/4/2/org/3/2`: `OldMassGauge` (wrapper)

Source `the November 2 reference manuscript` 5527 (`N ≤ P_ν|N_ν|‖g⁻¹T‖_Z`),
5573-5576 (the mass `N_0`). The proof is `MassGaugeOrg.oldMassGauge_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`OldMassGauge`** (source 5527). -/
theorem oldMassGauge (dm dp : ℝ) : OldMassGauge dm dp :=
  MassGaugeOrg.oldMassGauge_proof dm dp

end UnforcedLeray.Short.PartIIIb.Concrete
