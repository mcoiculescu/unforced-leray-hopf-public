import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PartIIIb_C_near_masked_22
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.Strip.Split
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.Strip.Near
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.Strip.Far

/-!
# `stripKernelBound_of`: the partial-strip kernel bound from the kernel and Young hypotheses

Source of record: `the November 2 reference manuscript`, lines 3996-4005.

`StripKernelBound` is assembled from the three parts `StripSplit`, `StripNear`, `StripFar`
(decomposition `stripKernelBound_of_parts`), each proved from `SepKernelBounds` and `SepYoung`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- **`stripKernelBound_of`** (source 3996-4005): the partial-strip kernel bound, from the
separated kernel bounds and the separated Young hypothesis. -/
theorem stripKernelBound_of (hK : UnforcedLeray.Short.IIIa.SepKernelBounds)
    (hY : UnforcedLeray.Short.IIIa.SepYoung) : StripKernelBound :=
  stripKernelBound_of_parts (stripSplit_holds hK) (stripNear_holds hK hY) (stripFar_holds hK hY)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
