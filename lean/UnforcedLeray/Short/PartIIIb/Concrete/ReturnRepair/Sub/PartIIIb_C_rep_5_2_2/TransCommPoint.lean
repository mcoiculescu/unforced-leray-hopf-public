import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Reg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Int
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Time
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Grad
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Lap
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Rad
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Leibniz
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Coeff

/-!
# `PartIII-b:C/rep/5/2/2/11` : `TransCommPoint` from the eight leaves

Source `the November 2 reference manuscript`
3700-3712 (commutator `𝒬`), 4176-4214 (outward primitive).

Assembles `transCommPoint_of` (Sub `PartIII-b_C_rep_5_2_2_11`) from the leaves
`tcReg`, `tcInt`, `tcTime`, `tcGrad`, `tcLap`, `tcRad`, `tcLeibniz`, `tcCoeff`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`TransCommPoint`** (the transition commutator bound), from the eight leaves. -/
theorem transCommPoint : TransCommPoint :=
  transCommPoint_of tcReg tcInt tcTime tcGrad tcLap tcRad tcLeibniz tcCoeff

end UnforcedLeray.Short.PartIIIb.Concrete
