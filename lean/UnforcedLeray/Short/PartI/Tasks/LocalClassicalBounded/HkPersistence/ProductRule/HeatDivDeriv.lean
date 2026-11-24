import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule.HeatDivDeriv.KernelSmooth
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule.HeatDivDeriv.SmoothOutput
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule.HeatDivDeriv.Bridges

/-!
# Part I, task `PartI:T02/1/2/3/5`: `∂_j` commutes with `G ↦ e^{θΔ} div G` on tensor `H³`

Source of record: `the November 2 reference manuscript`, lines 261-288.
If `G' ∈ H³` is the periodic weak `∂_j`-derivative of the tensor `G ∈ H³`, then
`e^{θΔ} div G'` is the periodic weak `∂_j`-derivative of `e^{θΔ} div G`.

Proof (helpers in `ProductRule/HeatDivDeriv/`): every normalized derivative component of
`e^{θΔ} div G` is `e^{θΔ} div` of the normalized kernel class of the same derivative of `G`
(`bdpHddRough_of`, by density from the smooth identities `bdpHddKernelSmooth_proof` and
`bdpHddSmoothOutput_proof`); the weak-derivative relation is the equality of the `∂_j` component
with the value component (`bdpHddTensorBridge_proof`, `bdpHddVectorBridge_proof`).
No `sorry`, `admit`, `axiom` or `native_decide`.
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
open UnforcedLeray.HeatCylinder

theorem bdp_actualHeatDivH3CLM_hasWeakDeriv {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (j : Fin 2)
    (G G' : TensorH3 c) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val G : Plane → TensorVal) (Cyl.H.val G' : Plane → TensorVal) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (actualHeatDivH3CLM hc hθ G) : Plane → Vec)
      (Cyl.H.val (actualHeatDivH3CLM hc hθ G') : Plane → Vec) :=
  bdp_actualHeatDivH3CLM_hasWeakDeriv_of' bdpHddKernelSmooth_proof bdpHddSmoothOutput_proof
    bdpHddTensorBridge_proof bdpHddVectorBridge_proof hc hθ j G G'

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.bdp_actualHeatDivH3CLM_hasWeakDeriv
