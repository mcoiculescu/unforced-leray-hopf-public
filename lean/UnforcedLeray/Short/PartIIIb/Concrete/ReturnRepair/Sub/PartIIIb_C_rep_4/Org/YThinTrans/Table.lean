import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.TableOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.MassGauge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.AnnulusFields
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.MultStep

/-!
# `PartIII-b:C/rep/4/2/org/3`: `TransThinTable`

Source `the November 2 reference manuscript` 5312-5355, 5573-5592, 5527.
Assembles `OldMassGauge`, `AnnulusFields`, and `TransMultiplierStep` via `transThinTable_of`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The thin-source table row for both transitions** (source 5312-5355, 5573-5592). -/
theorem transThinTable (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : TransThinTable Pl σ₀ mZ dm dp :=
  transThinTable_of (oldMassGauge dm dp) (annulusFields dm dp) (transMultiplierStep Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete

end
