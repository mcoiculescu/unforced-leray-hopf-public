import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_22_2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.Strip.Near.Q1
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.Strip.Near.Q2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.Strip.Near.Q3
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.Strip.Near.Q4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.Strip.Near.Q5
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.Strip.Near.Q6

/-!
# `PartIII-b:C/near/masked/22/2/7`: `StripNear` from the six leaves (source 4000-4003)

Source of record: `the November 2 reference manuscript`, lines 4000-4003.

The strip near part is assembled from the leaves: pointwise bound (Q1), measurability and
periodicity (Q2), rotation covariance (Q3, used by Q4), axisymmetry (Q4), `sep:young` (Q5) and the
source norm bound (Q6). The Young hypothesis is `hY`; the kernel-bounds hypothesis is not needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

theorem stripNear_holds (hK : UnforcedLeray.Short.IIIa.SepKernelBounds)
    (hY : UnforcedLeray.Short.IIIa.SepYoung) : StripNear :=
  stripNear_holds_of nearPointwise_holds nearMeasPeriodic_holds nearAxisym_holds
    nearYoung_holds nearSource_holds hY

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
