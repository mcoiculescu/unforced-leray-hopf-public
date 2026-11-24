import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.BridgeProof
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.ThinRecvProof

/-!
# `PartIII-b:C/rep/4/4/1/org/7/1`: `EarlyRepThinKernel`

Source `the November 2 reference manuscript` lines 5303-5308, 5318-5319,
5323-5339 ("the repair-to-thin entry uses the pointwise exponent 79/22"), 3593-3594, 3902-3920.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem earlyRepThinKernel (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : EarlyRepThinKernel Pl σ₀ mZ dm dp :=
  earlyRepThinKernel_of Pl σ₀ mZ dm dp (earlyFarSepBridge Pl σ₀ mZ dm dp) (farThinRecv Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
