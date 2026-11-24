import UnforcedLeray.Short.PartI.Sub.PartI_T15
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay.DuhamelSplit

/-!
# `PartI:T15` (`OverlapMeanDecay.lean`): algebraic decay of the overlap horizontal mean

Source of record: `the November 2 reference manuscript`, lines 304-313, 415-425
(old lines 425-436).

Assembles `overlap_mean_decay` from `overlap_mean_decay_of` (`UnforcedLeray.Short.PartI.Sub.PartI_T15`)
and the 1D heat Duhamel split leaf `overlap_mean_duhamel_split`
(`UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay.DuhamelSplit`, `PartI:T15/1`).
-/

namespace UnforcedLeray.Short.PartI

theorem overlap_mean_decay (hHN : OverlapHighNormUniform) (hFD : OverlapFluctuationDecay) (hMP : OverlapMeanPrimitive) : OverlapMeanDecay :=
  overlap_mean_decay_of hHN hFD hMP overlap_mean_duhamel_split

end UnforcedLeray.Short.PartI
