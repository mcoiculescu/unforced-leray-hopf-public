import UnforcedLeray.Lib.HeatCylinder.H3RoughOrbitContinuity
import UnforcedLeray.Lib.HeatCylinder.H3Density
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3DerivativeComponents

/-!
# Part I, task `PartI:T02/1/2/3/5`: `∂_j` commutes with `G ↦ e^{θΔ} div G` (design)

Source of record: `the November 2 reference manuscript`, lines 261-288 (the mild
`H³` solution is differentiated along the cylinder directions; the Duhamel term needs that the
weak `∂_j`-derivative commutes with the heat-divergence map `G ↦ e^{θΔ} div G`).

Route (derivative components, no translation group).  The library already identifies every
ordered derivative component of the actual smooth output `heatDivH3` with the actual
normalized-cell Gaussian orbit on the matching input derivative
(`Lib/HeatCylinder/H3SmoothDerivativeBridge.lean`), and it has the template for rough inputs in
the heat case (`vectorH3DerivativeNormalizedValue_actualHeatVecH3`,
`Lib/HeatCylinder/HeatVecH3DerivativeComponentsRough.lean`).  Here:

* `bdpTensorH3DerivKernel hc α G` is the concrete normalized-cell kernel class of the weak
  derivative `∂^α G` (centered cell → normalized B0284 cell, rows transported by the actual
  vector transport `centeredVecToNormalizedCLM`).  It factors through `W.deriv α G` by definition.
* `BdpHddKernelSmooth` (leaf A1): on smooth inputs it is the literal derivative class.
* `BdpHddSmoothOutput` (leaf A2): every normalized derivative component of the smooth output
  `heatDivH3` is `heatDivVecL2CLM` of the literal input derivative.
* `BdpHddRough` (proved here from A1, A2 by density): for every `G ∈ H³` and every word `α`,
  `∂^α (e^{θΔ} div G) = e^{θΔ} div (∂^α G)` at the normalized `L²` level.
* `BdpHddTensorBridge` (leaf B), `BdpHddVectorBridge` (leaf C): the weak-derivative relation in
  terms of `W.deriv` components, on the tensor input side and the vector output side.

The target `bdp_actualHeatDivH3CLM_hasWeakDeriv` is `bdp_actualHeatDivH3CLM_hasWeakDeriv_of'`
applied to the four leaves.  No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane cellμ)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-! ### The normalized kernel class of a tensor derivative component -/

/-- The weighted cylinder measure of the train `H³` space is the centered cell measure; this is
the identity transport of tensor `L²` classes between the two (equal) measures. -/
noncomputable def bdpTensorWeightedToCellCLM (c : ℝ) :
    Lp TensorVal 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) →L[ℝ]
      Lp TensorVal 2 (cellμ c) := by
  have hμ := heatVecH3_measure_eq_cell_deriv c
  have hle : cellμ c ≤ (1 : ℝ≥0∞) • Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) := by
    rw [← hμ]
    simp
  exact Lp.LpToLpOfMeasureLeSMul (μ := cellμ c)
    (ν := Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) (c := 1) (by simp) hle

/-- First row of a row tensor as a train vector (`toVec ∘ fst ∘ tensorToPlaneCLE`). -/
noncomputable def bdpTensorRow₁CLM : TensorVal →L[ℝ] Vec :=
  (Train.toVecL : Plane →L[ℝ] Vec).comp
    ((ContinuousLinearMap.fst ℝ Plane Plane).comp tensorToPlaneCLE.toContinuousLinearMap)

/-- Second row of a row tensor as a train vector (`toVec ∘ snd ∘ tensorToPlaneCLE`). -/
noncomputable def bdpTensorRow₂CLM : TensorVal →L[ℝ] Vec :=
  (Train.toVecL : Plane →L[ℝ] Vec).comp
    ((ContinuousLinearMap.snd ℝ Plane Plane).comp tensorToPlaneCLE.toContinuousLinearMap)

/-- Centered-cell tensor class → normalized-cell kernel class in the product-plane carrier of
B0296's `heatDiv`: each row is sent through the actual centered periodic extension
`centeredVecToNormalizedCLM`, then the rows are reassembled in `Plane × Plane`. -/
noncomputable def bdpCellToKernelCLM {c : ℝ} (hc : 0 < c) :
    Lp TensorVal 2 (cellμ c) →L[ℝ] Lp (Plane × Plane) 2 (UnforcedLeray.B0284.cellMeasure c) :=
  (((ContinuousLinearMap.inl ℝ Plane Plane).comp
      (Train.toVecL.symm : Vec →L[ℝ] Plane)).compLpL 2
      (UnforcedLeray.B0284.cellMeasure c)).comp
    ((centeredVecToNormalizedCLM hc).comp (bdpTensorRow₁CLM.compLpL 2 (cellμ c))) +
  (((ContinuousLinearMap.inr ℝ Plane Plane).comp
      (Train.toVecL.symm : Vec →L[ℝ] Plane)).compLpL 2
      (UnforcedLeray.B0284.cellMeasure c)).comp
    ((centeredVecToNormalizedCLM hc).comp (bdpTensorRow₂CLM.compLpL 2 (cellμ c)))

/-- The normalized-cell kernel class of the weak derivative `∂^α G` of a tensor `H³` element:
the `L²` input that `heatDivVecL2CLM` sees for the derivative.  It factors through
`W.deriv α G` by definition. -/
noncomputable def bdpTensorH3DerivKernel {c : ℝ} (hc : 0 < c) (α : Sob.Idx 2 3) :
    TensorH3 c →L[ℝ] Lp (Plane × Plane) 2 (UnforcedLeray.B0284.cellMeasure c) :=
  (bdpCellToKernelCLM hc).comp ((bdpTensorWeightedToCellCLM c).comp
    (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 α))

theorem bdpTensorH3DerivKernel_apply {c : ℝ} (hc : 0 < c) (α : Sob.Idx 2 3) (G : TensorH3 c) :
    bdpTensorH3DerivKernel hc α G = bdpCellToKernelCLM hc (bdpTensorWeightedToCellCLM c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 α G)) := rfl

/-! ### The leaves -/

/-- **Leaf A1** (smooth input).  Source lines 261-288 (derivatives of smooth periodic data).
For a smooth periodic compact-axial tensor field `T`, the kernel class of `∂^α T` is the literal
normalized-cell class of the `α`-derivative of `tensorToPlaneCLE ∘ T`. -/
def BdpHddKernelSmooth : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (T : Plane → TensorVal) (hT : Sob.IsCylSmooth c T) (α : Sob.Idx 2 3),
    bdpTensorH3DerivKernel hc α
        (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := TensorVal) (k := 3)
          (p := 2) hc T hT) =
      (memLp_tensor_iterD_cylSmooth_normalized hc
          (isCylSmooth_postcomp_clm hT tensorToPlaneCLE.toContinuousLinearMap)
          ((Sob.cylinder c).word α)).toLp
        (Sob.iterD ((Sob.cylinder c).word α)
          (fun z => tensorToPlaneCLE.toContinuousLinearMap (T z)))

/-- **Leaf A2** (smooth output).  Source lines 261-288 (`∂_j` commutes with `e^{θΔ} div` on smooth
data).  Every normalized derivative component of the actual smooth Gaussian output `heatDivH3`
is the actual normalized-cell Gaussian heat-divergence of the literal input derivative. -/
def BdpHddSmoothOutput : Prop :=
  ∀ (c θ : ℝ) (hc : 0 < c) (hθ : 0 < θ) (S : Plane → Plane × Plane)
    (hS : Sob.IsCylSmooth c S) (α : Sob.Idx 2 3),
    vectorH3DerivativeNormalizedValue hc α (heatDivH3 hc hθ hS) =
      heatDivVecL2CLM hc hθ
        ((memLp_tensor_iterD_cylSmooth_normalized hc hS ((Sob.cylinder c).word α)).toLp
          (Sob.iterD ((Sob.cylinder c).word α) S))

/-- **Rough commutation** (proved below from A1, A2).  Source lines 261-288.  For every tensor
`G ∈ H³`, every normalized derivative component of `e^{θΔ} div G` is `e^{θΔ} div` of the kernel
class of the same derivative of `G`. -/
def BdpHddRough : Prop :=
  ∀ (c θ : ℝ) (hc : 0 < c) (hθ : 0 < θ) (α : Sob.Idx 2 3) (G : TensorH3 c),
    vectorH3DerivativeNormalizedValue hc α (actualHeatDivH3CLM hc hθ G) =
      heatDivVecL2CLM hc hθ (bdpTensorH3DerivKernel hc α G)

/-- **Leaf B** (tensor input side).  Source lines 261-288.  If `G' ∈ H³` is the periodic weak
`∂_j`-derivative of `G ∈ H³`, then the `∂_j` component of `G` is the value component of `G'`
(uniqueness of weak derivatives). -/
def BdpHddTensorBridge : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (j : Fin 2) (G G' : TensorH3 c),
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val G : Plane → TensorVal) (Cyl.H.val G' : Plane → TensorVal) →
    Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) G =
      Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
        (Sob.Idx.zero : Sob.Idx 2 3) G'

/-- **Leaf C** (vector output side).  Source lines 261-288.  If the normalized `∂_j` component of
`Y ∈ H³` equals the normalized value component of `Y' ∈ H³`, then `Y'` is the periodic weak
`∂_j`-derivative of `Y`. -/
def BdpHddVectorBridge : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (j : Fin 2) (Y Y' : VectorH3 c),
    vectorH3DerivativeNormalizedValue hc (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) Y =
      vectorH3DerivativeNormalizedValue hc (Sob.Idx.zero : Sob.Idx 2 3) Y' →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val Y : Plane → Vec) (Cyl.H.val Y' : Plane → Vec)

/-! ### Assembly -/

/-- Density step: the smooth identities A1, A2 extend to every tensor `H³` element, because both
sides are continuous linear in `G` and smooth tensors are dense (`exists_smoothTensorH3_sequence`). -/
theorem bdpHddRough_of (h1 : BdpHddKernelSmooth) (h2 : BdpHddSmoothOutput) : BdpHddRough := by
  intro c θ hc hθ α G
  obtain ⟨y, T, hT, hyrep, hyLim⟩ := exists_smoothTensorH3_sequence hc G
  have hseq : (fun n => vectorH3DerivativeNormalizedValue hc α (actualHeatDivH3CLM hc hθ (y n))) =
      fun n => heatDivVecL2CLM hc hθ (bdpTensorH3DerivKernel hc α (y n)) := by
    funext n
    rw [hyrep n, actualHeatDivH3CLM_apply_ofCylSmooth hc hθ (hT n),
      h2 c θ hc hθ _ (isCylSmooth_postcomp_clm (hT n) tensorToPlaneCLE.toContinuousLinearMap) α,
      h1 c hc (T n) (hT n) α]
  have hlhs : Tendsto
      (fun n => vectorH3DerivativeNormalizedValue hc α (actualHeatDivH3CLM hc hθ (y n))) atTop
      (𝓝 (vectorH3DerivativeNormalizedValue hc α (actualHeatDivH3CLM hc hθ G))) :=
    (((vectorH3DerivativeNormalizedValue hc α).comp
      (actualHeatDivH3CLM hc hθ)).continuous.tendsto G).comp hyLim
  have hrhs : Tendsto
      (fun n => heatDivVecL2CLM hc hθ (bdpTensorH3DerivKernel hc α (y n))) atTop
      (𝓝 (heatDivVecL2CLM hc hθ (bdpTensorH3DerivKernel hc α G))) :=
    (((heatDivVecL2CLM hc hθ).comp (bdpTensorH3DerivKernel hc α)).continuous.tendsto G).comp
      hyLim
  rw [hseq] at hlhs
  exact tendsto_nhds_unique hlhs hrhs

/-- The target from the rough commutation and the two bridges. -/
theorem bdp_actualHeatDivH3CLM_hasWeakDeriv_of (hA : BdpHddRough) (hB : BdpHddTensorBridge)
    (hC : BdpHddVectorBridge) {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (j : Fin 2)
    (G G' : TensorH3 c) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val G : Plane → TensorVal) (Cyl.H.val G' : Plane → TensorVal) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (actualHeatDivH3CLM hc hθ G) : Plane → Vec)
      (Cyl.H.val (actualHeatDivH3CLM hc hθ G') : Plane → Vec) := by
  intro h
  apply hC c hc j
  rw [hA c θ hc hθ, hA c θ hc hθ, bdpTensorH3DerivKernel_apply, bdpTensorH3DerivKernel_apply,
    hB c hc j G G' h]

/-- The target from the four leaves A1, A2, B, C. -/
theorem bdp_actualHeatDivH3CLM_hasWeakDeriv_of' (h1 : BdpHddKernelSmooth)
    (h2 : BdpHddSmoothOutput) (hB : BdpHddTensorBridge) (hC : BdpHddVectorBridge)
    {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (j : Fin 2) (G G' : TensorH3 c) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val G : Plane → TensorVal) (Cyl.H.val G' : Plane → TensorVal) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (actualHeatDivH3CLM hc hθ G) : Plane → Vec)
      (Cyl.H.val (actualHeatDivH3CLM hc hθ G') : Plane → Vec) :=
  bdp_actualHeatDivH3CLM_hasWeakDeriv_of (bdpHddRough_of h1 h2) hB hC hc hθ j G G'

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.bdpHddRough_of
#print axioms UnforcedLeray.Short.PartI.bdp_actualHeatDivH3CLM_hasWeakDeriv_of
#print axioms UnforcedLeray.Short.PartI.bdp_actualHeatDivH3CLM_hasWeakDeriv_of'
