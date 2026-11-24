import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.DuhamelOf
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.FluxDuhamel
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.FluxContinuous

/-!
# Part III-a, `PartIII-a:T21/3/2/2/3`: the Duhamel identity `UnitHeatDuhamel` for `cylHeatSmooth`

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Assembly of `unitHeatDuhamel_of` (DuhamelOf), `fluxPairHeatDuhamel` (FluxDuhamel) and
`fluxPairHeatContinuous` (FluxContinuous).
-/

set_option autoImplicit false

open UnforcedLeray.Short.IIIa.Exist

theorem unitHeatDuhamel :
    UnforcedLeray.Short.IIIa.Exist.UnitHeatDuhamel UnforcedLeray.Short.IIIa.Exist.cylHeatSmooth :=
  UnforcedLeray.Short.IIIa.Exist.unitHeatDuhamel_of
    UnforcedLeray.Short.IIIa.Exist.fluxPairHeatDuhamel
    UnforcedLeray.Short.IIIa.Exist.fluxPairHeatContinuous
