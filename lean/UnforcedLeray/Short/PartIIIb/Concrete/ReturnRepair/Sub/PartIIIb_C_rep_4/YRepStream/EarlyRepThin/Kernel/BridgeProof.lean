import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.Bridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.StrBoxTrunc
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.EarlySrcStrSum
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.SopSubIsFar

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem earlyFarSepBridge (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : EarlyFarSepBridge Pl σ₀ mZ dm dp :=
  earlyFarSepBridge_of Pl σ₀ mZ dm dp strBoxTrunc earlySrcStrSum (sopSubIsFarSeq Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
