import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3.Tail
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_3_1.Core

/-!
# `PartIII-b:C/rep/5/1/1/3/3/1`: the box-level single-term bound `tailBoxBinSeq`

Source `the November 2 reference manuscript`
5585-5593. The thin-stress form `tailBoxThinSeq'` (Core) is converted to the box-level
single-term bound `TailBoxBinSeq` by `tailBoxBinSeq_of` (Tail), which uses the thin mass bound
`thinMassBoundSlice`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tailBoxBinSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : TailBoxBinSeq Pl σ₀ mZ dm dp :=
  tailBoxBinSeq_of Pl σ₀ mZ dm dp (tailBoxThinSeq' Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete

end
