import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1_1
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.PlaneHeatGradSmoothing.GaussGradL1
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.PlaneHeatGradSmoothing.PlaneHeatGradIBP
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.PlaneHeatGradSmoothing.CellYoungKernel

/-!
# `PartII-a:N01/9/1/3/3/2/1/1`: `PlaneHeatGradSmoothing`

Source `the November 2 reference manuscript`
lines 3373-3383, 1684-1689.  Assembly of `GaussGradL1` (K1), `PlaneHeatGradIBP` (K2) and
`CellYoungKernel` (K3) through `planeHeatGradSmoothing_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

theorem planeHeatGradSmoothing : UnforcedLeray.Short.PartIIa.N01.PlaneHeatGradSmoothing :=
  UnforcedLeray.Short.PartIIa.N01.planeHeatGradSmoothing_of
    gaussGradL1 planeHeatGradIBP cellYoungKernel

end UnforcedLeray.Short.PartIIa.N01
