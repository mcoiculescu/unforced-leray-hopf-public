import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_5
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressMapWeakSol.Str
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressMapWeakSol.Smooth
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressMapWeakSol.Density
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressMapWeakSol.Closed

/-!
# `PartIII-b:C/near/pins/5`: `StressMapWeakSol` from four leaves

Source `the November 2 reference manuscript`
3888-3890, 1675-1679, 1556-1572.

`stressMapWeakSol_assemble` (Sub 5) reduces `StressMapWeakSol` to the four leaf properties
`SWStrTv4`, `SWSmooth`, `SWDensity`, `SWClosed`, proved in `Proofs/StressMapWeakSol/{Str,Smooth,
Density,Closed}.lean` as `swStrTv4`, `swSmooth`, `swDensity`, `swClosed`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

theorem stressMapWeakSol_of (hT : TepsWeakSol) (hC : ChartDivPair) (hD : Masked.TensorTestDense)
    (hM : Masked.TensorTestDivMem) (hHT : ∀ c : ℝ, 0 < c → Masked.CellPtHT c)
    (hH : ∀ c : ℝ, 0 < c → Masked.CellPtH c) (hHi : ∀ c : ℝ, 0 < c → Masked.CellPtInvH c) :
    StressMapWeakSol :=
  stressMapWeakSol_assemble swStrTv4 swSmooth swDensity swClosed hT hC hD hM hHT hH hHi

end UnforcedLeray.Short.PartIIIb.NearInst
