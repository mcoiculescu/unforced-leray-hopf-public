import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCircLeaves
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.CellIntegrable
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.CutoffTest
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.ChiDeriv
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.BandL2
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.CauchySchwarz
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.CutoffLimit

/-!
# Part III-a full clock: zero circulation is preserved (task `PartIII-a:T21/1`)

Source: `the November 2 reference manuscript` lines 3100-3101. The statement
`ZeroCirculationPreserved` (`Clock/Stages.lean`) is proved from the six leaves in
`Clock/Sub/ZeroCirc/*.lean` via `zeroCirculationPreserved_of` (`Clock/Sub/ZeroCircLeaves.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem zeroCirculationPreserved : UnforcedLeray.Short.IIIa.ZeroCirculationPreserved :=
  zeroCirculationPreserved_of zcCellIntegrable zcCutoffTest zcChiDeriv zcBandL2 zcCauchySchwarz
    zcCutoffLimit

end UnforcedLeray.Short.IIIa
