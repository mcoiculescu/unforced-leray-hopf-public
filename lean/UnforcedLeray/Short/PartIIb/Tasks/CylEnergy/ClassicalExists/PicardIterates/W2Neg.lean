import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_14

/-!

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

theorem pd_neg_fun (j : Fin 2) (g : B0579.Plane → ℝ) :
    B0579.pd j (fun y => -g y) = fun y => -B0579.pd j g y := by
  funext x
  unfold B0579.pd
  simp

/-- **`PartII-b:T22/1/14/3`** `W2 (-g) = W2 g`. -/
theorem w2Neg_proof : UnforcedLeray.Short.IIb.CylPDE.W2Neg := by
  intro g x
  unfold W2
  simp only [pd_neg_fun, abs_neg]

end CylPDE

end UnforcedLeray.Short.IIb

end
