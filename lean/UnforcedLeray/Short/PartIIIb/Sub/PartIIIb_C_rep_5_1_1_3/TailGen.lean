import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3.Tail
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3.TailBoxBin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_2_2.Transfer

/-!
# `PartIII-b:C/rep/5/1/1/3/3`: the tail thin-stress bin estimate (sequence form)

Source `the November 2 reference manuscript` 5585-5593 (single-term bound).
The box-level estimate `tailBoxBinSeq` is turned into thin stresses by the density transfer
`binDensityTransfer` (3905-3912), via `tailBinGenSeq_of`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal Classical
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tailBinGenSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : TailBinGenSeq Pl σ₀ mZ dm dp :=
  tailBinGenSeq_of Pl σ₀ mZ dm dp binDensityTransfer (tailBoxBinSeq Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete

end
