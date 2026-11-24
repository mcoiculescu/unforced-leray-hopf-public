import UnforcedLeray.Short.PartIIa.Sub.N02_4_11_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncConverge.SliceToL2.NzsTruncCont
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncConverge.SliceToL2.NzsFubini
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncConverge.SliceToL2.NzsBandFinite
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncConverge.SliceToL2.NzsSliceLintegral
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncConverge.SliceToL2.NzsBound

/-!
# Part II-a, `PartII-a:N02/4/11/2` (`nzSliceToL2`): assembly

Source of record: `the November 2 reference manuscript`, lines 1744-1749.

The five elementary facts `NzsTruncCont`, `NzsFubini`, `NzsBandFinite`, `NzsSliceLintegral`,
`NzsBound` are proved in the sibling leaf files `TruncConverge/SliceToL2/`; this file feeds them to
`nzSliceToL2_of` from `Sub/N02_4_11_2.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

theorem nzSliceToL2 : UnforcedLeray.Short.PartIIa.NzSliceToL2 :=
  nzSliceToL2_of nzsTruncCont nzsFubini nzsBandFinite nzsSliceLintegral nzsBound

end UnforcedLeray.Short.PartIIa
