import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.ProductFull

/-!
# `PartIII-b:C/rep/4/4/1/org/6`: `lateRepRep`

`LateRepRep` from the separated kernel (`lateSepKernel`) and the repair product estimate
(`repairProductAll`), via `lateRepRep_of` (`LateRepRep/Props.lean`).
-/

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem lateRepRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : LateRepRep Pl σ₀ mZ dm dp :=
  lateRepRep_of Pl σ₀ mZ dm dp (lateSepKernel Pl σ₀ mZ dm dp) (repairProductAll dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
