import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepRep.Kernel.Ungained
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepRep.Kernel.FarUng

/-!
# `PartIII-b:C/rep/4/4/1/org/8/1`: `earlyRepRepKernel`

Source `the November 2 reference manuscript` 5303-5308, 5323-5339.

The statement `EarlyRepRepKernel` is proved from the shared leaf `farRepRepUng`
(`Kernel/FarUng.lean`) by `earlyRepRepKernel_of_farRepRepUng` (`Kernel/Ungained.lean`).
-/

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem earlyRepRepKernel (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : EarlyRepRepKernel Pl σ₀ mZ dm dp :=
  earlyRepRepKernel_of_farRepRepUng Pl σ₀ mZ dm dp (farRepRepUng Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
