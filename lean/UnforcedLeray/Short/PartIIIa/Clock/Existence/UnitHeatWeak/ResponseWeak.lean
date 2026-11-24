import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.LinComm
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.Dual
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.Duhamel

/-!
# Part III-a, `PartIII-a:T21/3/2/2`: `UnitHeatResponseWeak` from the dual heat pairing

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Assembly of `unitHeatResponseWeak_of` (Sub/PartIIIa_T21_3_2_2.lean) with the three inputs
`unitHeatLinComm` (N4), `unitHeatDual` (N2) and `unitHeatDuhamel` (N3), instantiated at the
concrete smoothing `cylHeatSmooth`.
-/

set_option autoImplicit false

theorem unitHeatResponseWeak : UnforcedLeray.Short.IIIa.Exist.UnitHeatResponseWeak :=
  UnforcedLeray.Short.IIIa.Exist.unitHeatResponseWeak_of
    UnforcedLeray.Short.IIIa.Exist.cylHeatSmooth
    UnforcedLeray.Short.IIIa.Exist.unitHeatLinComm
    UnforcedLeray.Short.IIIa.Exist.unitHeatDual
    unitHeatDuhamel
