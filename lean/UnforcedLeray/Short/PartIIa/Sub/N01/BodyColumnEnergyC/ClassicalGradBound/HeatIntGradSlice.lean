import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1_2
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.HeatIntGradSlice.GradSliceMeas
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.HeatIntGradSlice.GradSliceL2

/-!
# `PartII-a:N01/9/1/3/3/2/1/2`: `heatIntGradSlice`

Source `the November 2 reference manuscript`
lines 1684-1689, 3379-3383.  Assembly: `heatIntGradSlice_of` applied to the joint measurability
`gradSliceMeas` and the per-`σ` smoothing bound `gradSliceL2`.
-/

set_option autoImplicit false

theorem heatIntGradSlice : UnforcedLeray.Short.PartIIa.N01.HeatIntGradSlice :=
  UnforcedLeray.Short.PartIIa.N01.HIGS.heatIntGradSlice_of gradSliceMeas gradSliceL2
