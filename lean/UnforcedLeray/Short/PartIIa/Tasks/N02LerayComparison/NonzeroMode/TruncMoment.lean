import UnforcedLeray.Short.PartIIa.Sub.N02_4_10
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncMoment.STest
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncMoment.TruncTest
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncMoment.Comm
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncMoment.BesselPt
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncMoment.MeasureMono

/-!
# Part II-a, task `PartII-a:N02/4/10` (`nzTruncMoment`): assembly

Source of record: `the November 2 reference manuscript` lines 1744-1749.
The five leaves (`ntmSTest`, `ntmTruncTest`, `ntmComm`, `ntmBesselPt`, `ntmMeasureMono`) are
compiled in `TruncMoment/`; `nzTruncMoment_of` (Sub/N02_4_10.lean) assembles them.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem nzTruncMoment : UnforcedLeray.Short.PartIIa.NzTruncMoment :=
  nzTruncMoment_of ntmSTest ntmTruncTest ntmComm ntmBesselPt ntmMeasureMono

end UnforcedLeray.Short.PartIIa
