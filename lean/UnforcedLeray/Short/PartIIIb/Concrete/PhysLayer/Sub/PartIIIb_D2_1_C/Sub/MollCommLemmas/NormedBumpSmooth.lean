import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs

/-!
# `NormedBumpSmooth`: the normalised bump is smooth with compact support

Source `the November 2 reference manuscript` (the periodised bump of the
mollified pairing); the Lean definition of `NormedBumpSmooth` is in `MollCommDefs`.
Mathlib: `ContDiffBump.contDiff_normed`, `ContDiffBump.hasCompactSupport_normed`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem normedBumpSmooth : NormedBumpSmooth := by
  intro ρ
  exact ⟨ρ.contDiff_normed, ρ.hasCompactSupport_normed⟩

end UnforcedLeray.Short.PartIIIb.Concrete
