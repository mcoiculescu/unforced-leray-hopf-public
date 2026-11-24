import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4
import UnforcedLeray.Lib.HeatCylinder.HeatL2StrongContinuity

/-!
# Part I, task `PartI:T02/1/4/6/4`, leaf 3: the centered heat orbit is continuous in `L²`

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic: the Duhamel term of the mild solution is the heat flow of `div (u ⊗ u)`).
Target: `CenteredHeatContinuity`, defined in `Short/PartI/Sub/T02_1_4_6_4.lean`.

Proof. By definition `centeredHeatVecL2CLM hc θ` is the composite
`normalizedVecToCenteredCLM hc ∘ heatVecL2CLM hc θ ∘ centeredVecToNormalizedCLM hc`, and
`heatVecL2CLM hc θ` is `toVecL ∘ heatL2CLM hc θ ∘ toVecL.symm` on the normalized cell. Fix `x`
and put `y` for the Plane-valued class `toVecL.symm (centeredVecToNormalizedCLM hc x)`. Then, with the
fixed continuous linear map `L := normalizedVecToCenteredCLM hc ∘ toVecL`, the orbit is
`θ ↦ L (heatL2CLM hc θ y)`. The map `θ ↦ heatL2CLM hc θ y` is continuous on all of `ℝ`
(`continuous_heatL2CLM_apply`), so the orbit is continuous.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-- **Leaf 3** (`CenteredHeatContinuity`): for every `L²` class `x` on the centered cell, the
orbit `θ ↦ e^{θΔ} x` is continuous `ℝ → L²(cell)`. -/
theorem centeredHeatContinuity : CenteredHeatContinuity := by
  intro c hc x
  let y : Lp Plane 2 (UnforcedLeray.B0284.cellMeasure c) :=
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2
      (UnforcedLeray.B0284.cellMeasure c) (centeredVecToNormalizedCLM hc x)
  let L : Lp Plane 2 (UnforcedLeray.B0284.cellMeasure c) →L[ℝ] UnforcedLeray.Cyl.L2v c :=
    (normalizedVecToCenteredCLM hc).comp
      ((UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2
        (UnforcedLeray.B0284.cellMeasure c))
  have hfun : (fun θ : ℝ => centeredHeatVecL2CLM hc θ x) =
      fun θ : ℝ => L (heatL2CLM hc θ y) := by
    funext θ
    rfl
  rw [hfun]
  exact L.continuous.comp (continuous_heatL2CLM_apply hc y)

end UnforcedLeray.Short.PartI
