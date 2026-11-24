import UnforcedLeray.Short.PartIIIa.Clock.Sub.ShortWeakSmoothing
import UnforcedLeray.Short.PartIIIa.T21_2_WeakSmoothing
import UnforcedLeray.Short.PartIIIa.T06_ScalingJa
import UnforcedLeray.Short.PartIIIa.T07_ScalingJaInv
import UnforcedLeray.Short.PartIIIa.T08_ScalingJaInvDual
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.CellIntegrable
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.CutoffTest
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.ChiDeriv
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.BandL2
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.CauchySchwarz
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.CutoffLimit

/-!
# Part III-a full clock: short weak smoothing (task `PartIII-a:T21/5/short`)

Source of record: `the November 2 reference manuscript`, lines 3040-3094.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem shortWeakSmoothing : UnforcedLeray.Short.IIIa.ShortWeakSmoothing :=
  shortWeakSmoothing_of
    (fun m hm =>
      weakSmoothingPhys m hm (scalingBounds_of_parts scalingJa scalingJaInv scalingJaInvDual))
    (zeroCircInitial_of zcCellIntegrable zcCutoffTest zcChiDeriv zcBandL2 zcCauchySchwarz
      zcCutoffLimit)

end UnforcedLeray.Short.IIIa
