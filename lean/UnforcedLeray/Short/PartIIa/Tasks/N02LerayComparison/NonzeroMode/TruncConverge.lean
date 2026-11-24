import UnforcedLeray.Short.PartIIa.Sub.N02_4_11
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncConverge.SliceConv
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncConverge.SliceToL2

/-!
# Part II-a, `PartII-a:N02/4/11`: `nzTruncConverge` from slice convergence and Fubini/DCT

Target: `nzTruncConverge : NzTruncConverge` (`Sub/N02_4_2.lean`). Source of record:
`the November 2 reference manuscript`, lines 1744-1749.

The two leaves are `nzSliceConv` (`TruncConverge/SliceConv.lean`, `PartII-a:N02/4/11/1`) and
`nzSliceToL2` (`TruncConverge/SliceToL2.lean`, `PartII-a:N02/4/11/2`); the decomposition
`nzTruncConverge_of` is in `Sub/N02_4_11.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

theorem nzTruncConverge : UnforcedLeray.Short.PartIIa.NzTruncConverge :=
  nzTruncConverge_of nzSliceConv nzSliceToL2

end UnforcedLeray.Short.PartIIa
