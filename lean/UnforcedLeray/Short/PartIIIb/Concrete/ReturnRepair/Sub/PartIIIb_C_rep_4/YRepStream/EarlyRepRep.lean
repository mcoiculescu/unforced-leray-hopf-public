import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepRep.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepRep.Kernel
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Product

/-!
# `PartIII-b:C/rep/4/4/1/org/8`: `earlyRepRep`

Source `the November 2 reference manuscript` 5318-5319, 5323-5339.
The statement is the table entry `ε^{79/22}e^{3m₀/(2ν)}` for early source, repair source to
scaled repair receiver. It is the composition of `earlyRepRepKernel` (task `org/8/1`),
`earlyRepThinProduct` (task `org/7/2`) and the packaging lemma `earlyRepRep_of` (`EarlyRepRep/Props.lean`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem earlyRepRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : EarlyRepRep Pl σ₀ mZ dm dp :=
  earlyRepRep_of Pl σ₀ mZ dm dp (earlyRepRepKernel Pl σ₀ mZ dm dp) (earlyRepThinProduct Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete

end
