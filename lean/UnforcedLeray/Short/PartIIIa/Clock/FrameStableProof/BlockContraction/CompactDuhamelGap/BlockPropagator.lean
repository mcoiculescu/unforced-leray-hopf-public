import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_E

/-!
# `PartIII-a:T21/c3/2/1/1`: `DampedComplBlockPropagatorE`

Source of record: `the November 2 reference manuscript` (SP), lines 2919-2928,
2937-2982.

Assembles `dampedComplBlockPropagatorE` from `dampedComplBlockPropagatorE_proved` in
`UnforcedLeray.Short.«PartIII-a».Sub.«PartIII-a_T21_c3_2_1_E»`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem dampedComplBlockPropagatorE (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.DampedComplBlockPropagatorE κ :=
  dampedComplBlockPropagatorE_proved κ

end UnforcedLeray.Short.IIIa
