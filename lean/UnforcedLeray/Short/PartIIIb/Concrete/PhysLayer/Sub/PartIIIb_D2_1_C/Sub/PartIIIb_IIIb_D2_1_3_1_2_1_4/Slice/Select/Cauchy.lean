import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Cauchy.SliceEnergy
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Cauchy.SliceAe
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Cauchy.LapDiff
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Cauchy.WeakDiff
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Cauchy.YEnergy
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Cauchy.EnnrealCauchy
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Cauchy.YConvCauchy
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Cauchy.YrSub

/-!
# `selCauchy`: derivative Cauchy estimate on slices

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
The assembly `selCauchyY_of` (module `PartIII-b_IIIb-D2_1_3_1_2_1_4_1_3_2`) takes the eight
analytic Props, each proved in its own module under `Select/Cauchy/`:
slice energy (`SliceEnergy`, via `sliceH1`), slice a.e. membership (`SliceAe`), Laplacian and weak
derivative linearity (`LapDiff`, `WeakDiff`), `Y_2` energy by Cauchy-Schwarz in `τ` (`YEnergy`),
`ℝ≥0∞` Cauchy bookkeeping (`EnnrealCauchy`), convergence implies Cauchy (`YConvCauchy`) and
`Y_2` closed under differences (`YrSub`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem selCauchy : SelCauchy :=
  selCauchyY_of cSliceEnergy cSliceAe cLapDiff cWeakDiff cYEnergy cEnnrealCauchy cYConvCauchy cYrSub

end UnforcedLeray.Short.PartIIIb.Concrete
