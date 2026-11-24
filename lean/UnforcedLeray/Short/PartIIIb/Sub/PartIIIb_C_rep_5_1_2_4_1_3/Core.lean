import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Main
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.ChartMajSq
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.PsiMajMeasurable
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.PsiMajRotInv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.PsiMajPeriodic
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.ChartToPhys
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.PsiAtomsMinkowski
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.AtomBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.SourceMass
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.ConstAlgebra
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.BinNull

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3`: `WardYMajBinCore` from the proved leaves

Assembly of `WardYMajBinCore` (defined in `Sub/PartIII-b_C_rep_5_1_2_4_1_3.lean`) from the ten
leaf theorems, each proved in its own module. Source `the November 2 reference manuscript`
5585-5593.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`WardYMajBinCore` from the leaves** (source 5585-5593). -/
theorem wardYMajBinCore : WardYMajBinCore :=
  WYCore.wardYMajBinCore_of WYCore.chartMajSq WYCore.psiMajMeasurable WYCore.psiMajRotInv
    WYCore.psiMajPeriodic WYCore.chartToPhys WYCore.psiAtomsMinkowski WYCore.atomBound
    WYCore.sourceMass WYCore.constAlgebra WYCore.binNull

end UnforcedLeray.Short.PartIIIb.Concrete

end
