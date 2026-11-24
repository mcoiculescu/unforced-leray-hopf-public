import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_9

/-!
# Part III-a, `PartIII-a:T21/3/9/4`: the physical state space injects into functions

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Statement `VortFnInj` is in `Sub/PartIIIa_T21_3_9.lean`. Two elements of the physical state space
whose representatives agree a.e. on the cell are equal: `cellMeasure ≪ volume.restrict cell`
transfers the a.e. equality to `cellMeasure`, and `Lp.ext` plus `Subtype.ext` conclude.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

theorem vortFnInj : UnforcedLeray.Short.IIIa.Exist.VortFnInj := by
  intro c m _ hm w w' h
  have h2 : (⇑w.1 : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c m] (⇑w'.1 : ℝ × ℝ → ℝ) :=
    (B0579.cellMeasure_ac c m).ae_eq h
  exact Subtype.ext (Lp.ext h2)
