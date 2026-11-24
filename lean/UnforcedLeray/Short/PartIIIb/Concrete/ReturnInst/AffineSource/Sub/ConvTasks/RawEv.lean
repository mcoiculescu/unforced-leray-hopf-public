import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvGeoSub

/-!
# `convRawEv`: the raw lift agrees with the ring lift off the axis (`PartIII-b:C/asrc/ra/9/2/2/6`)

Source 2076-2077, 5200.  `Params.raw` is the ring lift of `rawProfile` extended through the axis
(`axisExt`), so off the axis it equals the ring lift (`Params.raw_eq_off_axis`).  The axis is
closed, so its complement is an open neighbourhood of every off-axis point.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

theorem convRawEv : ConvRawEv := by
  intro p τ y hy
  filter_upwards [isOpen_compl_axis.mem_nhds hy] with y' hy'
  exact p.raw_eq_off_axis τ y' hy'

end UnforcedLeray.Short.PartIIIb.Concrete
