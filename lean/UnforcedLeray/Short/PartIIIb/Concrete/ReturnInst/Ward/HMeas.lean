import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_6.L3

/-!
# `WardHMeas` (`PartIII-b:C/ward/7`)

Source of record: `the November 2 reference manuscript` 4171-4174, 4139-4141.
Measurability of the coefficient of `h` follows from `wardHMeas_of` applied to the
`C²`-off-axis regularity of `X` (`wardXDiffOffAxis_proved`, `PartIII-b:C/ward/6/3`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem wardHMeas_proved : WardHMeas :=
  wardHMeas_of wardXDiffOffAxis_proved

end UnforcedLeray.Short.PartIIIb.Concrete
