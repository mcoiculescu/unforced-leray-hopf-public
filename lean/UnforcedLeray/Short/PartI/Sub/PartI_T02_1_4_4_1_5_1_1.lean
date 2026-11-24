import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.Needed

/-!
# Part I, `PartI:T02/1/4/4/1/5/1/1`: decomposition of `HeatDivSmoothCase`

Source of record: `the November 2 reference manuscript`, lines 3594-3625
(smooth tensors first, then completion), and lines 261-288.

`HeatDivSmoothCase` follows from four sub-statements: the smooth representative of the tensor
class (`SmoothTensorRep`), the heat-divergence of a smooth tensor is the vector heat of its row
divergence (`SmoothTensorHeatIsVecHeat`), the pointwise calculus identity
`div(u ⊗ u) = (u·∇)u + (div u) u` (`RowDivTensorPointwise`), and the a.e. identification of
`A + E` with that smooth field (`AdvDivSmoothAe`).
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

/-- **Smooth tensor representative**, source 3594-3625: for `w ∈ H^5` with smooth cylinder
representative `u`, the class `res w ⊗ res w ∈ H^3` is `ofCylSmooth T` for a smooth cylinder
tensor `T` whose two-row form is `u ⊗ u` (`planeRowTensorValue u u`).  Proof: `res w =
ofCylSmooth u` at level 3 (`hVal_ext`), and `tensorH3Bilinear` of two smooth classes is the smooth
class of the pointwise product. -/
def SmoothTensorRep : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (hc1 : 1 ≤ c) (w : Cyl.H ℝ Cyl.Vec2 c 0 5) (u : Plane → Cyl.Vec2),
    Sob.IsCylSmooth c u → hVal w =ᵐ[(Sob.cylinder c).μ] u →
    ∃ (T : Plane → TensorVal) (hT : Sob.IsCylSmooth c T),
      tensorH3Bilinear hc1 (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3)
          (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) =
        Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := TensorVal) (k := 3) (p := 2)
          hc T hT ∧
      ∀ z, tensorToPlaneCLE (T z) = planeRowTensorValue u u z

/-- **Heat divergence of a smooth tensor is the vector heat of the row divergence**, source
3594-3625 (smooth tensors first): for a smooth cylinder tensor `T` and a class `X ∈ H^3` whose
value is a.e. the row divergence of `T`, the smooth Gaussian output `heatDivH3 T` equals the vector
heat semigroup `heatVecH3Semigroup` applied to `X`.  Proof: Gaussian integration by parts for
smooth bounded fields (`NeedSmoothRowIBP`, `NeedRowDivHeat`), then identification of the vector
heat on the normalized cell. -/
def SmoothTensorHeatIsVecHeat : Prop :=
  ∀ (c θ : ℝ) (hc : 0 < c) (hθ : 0 < θ) (T : Plane → TensorVal) (hT : Sob.IsCylSmooth c T)
    (X : Cyl.H ℝ Cyl.Vec2 c 0 3),
    (hVal X =ᵐ[Cyl.cellμ c] fun z =>
      toVec (rowDivergence (fun x => tensorToPlaneCLE (T x)) z)) →
    HeatCylinder.heatDivH3 hc hθ
        (HeatCylinder.isCylSmooth_postcomp_clm hT tensorToPlaneCLE.toContinuousLinearMap) =
      HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc X

/-- **Pointwise tensor divergence**, source 3594-3625: for a smooth `u`,
`∂_q(u₀ u) + ∂_η(u₁ u) = (u·∇)u + (div u) u` (no solenoidality). -/
def RowDivTensorPointwise : Prop :=
  ∀ (c : ℝ) (u : Plane → Cyl.Vec2), Sob.IsCylSmooth c u → ∀ z : Plane,
    toVec (rowDivergence (planeRowTensorValue u u) z) =
      Train.advection u z + (Cyl.divergence u z) • u z

/-- **A.e. identification of `A + E`**, source 261-288 and 3594-3625: if `w ∈ H^5` is a.e. the
smooth `u`, then `A + E` (advection term plus `(div w) w`) is a.e. `(u·∇)u + (div u) u`.  Proof:
`hVal (∂_i w) =ae ∂_i u` for the smooth representative, and `hVal_ext`-type a.e. calculus. -/
def AdvDivSmoothAe : Prop :=
  ∀ (c : ℝ) (w : Cyl.H ℝ Cyl.Vec2 c 0 5) (A E : Cyl.H ℝ Cyl.Vec2 c 0 3) (u : Plane → Cyl.Vec2),
    Sob.IsCylSmooth c u → hVal w =ᵐ[(Sob.cylinder c).μ] u → IsAdvectionTerm c w A →
    (hVal E =ᵐ[Cyl.cellμ c] fun z =>
      (∑ i : Fin 2, hVal (Sob.W.partialDeriv (k := 4) i w) z i) •
        hVal (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) z) →
    hVal (A + E) =ᵐ[Cyl.cellμ c] fun z => Train.advection u z + (Cyl.divergence u z) • u z

theorem heatDivSmoothCase_of (h1 : SmoothTensorRep) (h2 : SmoothTensorHeatIsVecHeat)
    (h3 : RowDivTensorPointwise) (h4 : AdvDivSmoothAe) : HeatDivSmoothCase := by
  intro c hc hc1 w A E hu hA hE θ hθ
  obtain ⟨u, hus, hwu⟩ := hu
  obtain ⟨T, hT, heq, hrow⟩ := h1 c hc hc1 w u hus hwu
  have hT' : (fun x => tensorToPlaneCLE (T x)) = planeRowTensorValue u u :=
    funext hrow
  have hae := h4 c w A E u hus hwu hA hE
  have hX : hVal (A + E) =ᵐ[Cyl.cellμ c] fun z =>
      toVec (rowDivergence (fun x => tensorToPlaneCLE (T x)) z) := by
    rw [hT']
    refine hae.trans (Filter.Eventually.of_forall fun z => ?_)
    exact (h3 c u hus z).symm
  have := h2 c θ hc hθ T hT (A + E) hX
  unfold HeatCylinder.actualHeatDivH3Orbit
  rw [dif_pos hθ, heq, HeatCylinder.actualHeatDivH3CLM_apply_ofCylSmooth hc hθ hT]
  exact this

end UnforcedLeray.Short.PartI
