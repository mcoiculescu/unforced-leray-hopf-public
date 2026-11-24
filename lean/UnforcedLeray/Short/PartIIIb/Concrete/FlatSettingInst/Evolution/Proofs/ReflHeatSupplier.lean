import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.Heat
import UnforcedLeray.Short.PartIIIa.Clock.Existence.ScaleSupplier

/-!
# Reflection-compatible rescaled heat supplier (source 2819-2836, 287-288)

Source of record: `the November 2 reference manuscript`, lines 2819-2836 and 287-288.
The rescaled physical heat supplier `ScaleAux.scaleHeat` satisfies the weak heat property with
diffusivity `ν` (`ScaleAux.scaledHeatWeak_scale`) and its reflection laws are those of the physical
supplier at age `ν * t`, by definitional unfolding.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol

/-- **`ReflHeatSupplierExists` from the unit weak property.** -/
theorem reflHeatSupplierExists_of
    (hU : UnforcedLeray.Short.IIIa.Exist.UnitHeatWeakActual) :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol.ReflHeatSupplierExists := by
  intro ν c m hF hc1 hm hν0 hν1
  refine ⟨UnforcedLeray.Short.IIIa.Exist.ScaleAux.scaleHeat hm
      (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualPhysicalWeightedHeatStripSupplier
        hc1 hm) ν hν0 hν1,
    UnforcedLeray.Short.IIIa.Exist.ScaleAux.scaledHeatWeak_scale hm _ ν hν0 hν1 (hU c m hc1 hm),
    fun t w => heatS0Refl_of periodicRepRefl c m hc1 hm (ν * t) w,
    fun t F => heatResponseRefl_of periodicRepRefl c m hc1 hm (ν * t) F⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol
