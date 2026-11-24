import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_6.L2a
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_6.L2b

/-!
# `WardX0FactsOldL2` (`PartIII-b:C/ward/6/2`)

Source of record: `the November 2 reference manuscript` 4161-4186, 3611-3621.
Assembled from `WardL2a` (smoothness, divergence, axisymmetry) and `WardL2b` (stream decay).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(L2) `X₀` regularity, structure and decay for old `L²` data** (source 4161-4186, 3611-3621). -/
theorem wardX0FactsOldL2_proved : WardX0FactsOldL2 := by
  intro ν μ R c hν hR hc hμ g hg
  exact ⟨fun τ => WardL2a.smooth ν μ R c g hν hR hc hμ hg τ,
    fun τ y hy => WardL2a.divFree ν μ R c g hν hR hc hμ hg τ y hy,
    WardL2a.axi ν μ R c g hν hR hc hμ hg,
    fun τ => WardL2b.decay ν μ R c g hν hR hc hμ hg τ⟩

end UnforcedLeray.Short.PartIIIb.Concrete
