import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanResMeasDefs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.RawLiftRegular.Raw
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.RawLiftRegular.Lift

/-!
# Regularity of the raw coefficient and the lifted pressure, along a train
(task `PartIII-b:C/rep/8/2/pres/6/2/pres`)

Source `the November 2 reference manuscript`
lines 1205-1225 (the lift is smooth through the axis for positive time), 1217, 5272-5282.

Composes the off-axis smoothness of the raw coefficient (`rawOffAxisSmooth_of`, needs the BUC class
of the train) and of the lifted pressure (`liftOffAxisSmooth_of`) with the axis continuity
hypothesis `RawAxisContinuous` through `rawLiftRegularAt_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped Classical

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- **Regularity of the raw coefficient and the lifted pressure** (source 1205-1225, 5272-5282),
for a level whose train is in the BUC class and whose raw coefficient is continuous through the
axis. -/
theorem rawLiftRegularAt (Pl : PlanarData) (L : ReturnLevel)
    (hb : UnforcedLeray.Short.PartI.IsBUCTrain L.train) (hAx : RawAxisContinuous Pl L) :
    RawLiftRegularAt Pl L :=
  rawLiftRegularAt_of Pl L (rawOffAxisSmooth_of Pl L hb) (liftOffAxisSmooth_of L) hAx

end UnforcedLeray.Short.PartIIIb.Concrete
