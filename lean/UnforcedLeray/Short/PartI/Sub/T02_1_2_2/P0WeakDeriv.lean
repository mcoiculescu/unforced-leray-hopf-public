import UnforcedLeray.Short.PartI.Sub.T02_1_2_2.WeakDerivCell

/-!
# Part I, task `PartI:T02/1/2/2`, leaf P: `P0WeakDeriv`

Source of record: `the November 2 reference manuscript`, lines 261-288.
`P0H3CLM` acts on every derivative component of an `H³` element by `Cyl.P0`
(`TrainB.P0H3CLM_apply_component`), so by the bridge `WeakDerivCell` it preserves the relation
"`y'` is the weak `∂_j`-derivative of `y`".  No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

theorem p0WeakDeriv_proof : P0WeakDeriv := by
  intro c hc j y y' h
  have h1 := (weakDerivCell_proof c hc j y y').mp h
  refine (weakDerivCell_proof c hc j _ _).mpr ?_
  rw [P0H3CLM_apply_component, P0H3CLM_apply_component, h1]

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.p0WeakDeriv_proof
