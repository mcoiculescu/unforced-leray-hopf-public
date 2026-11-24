import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5_1_1
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Semigroup
import UnforcedLeray.Lib.HeatCylinder.H3ValueLimit
import UnforcedLeray.Lib.HeatCylinder.H3ActualLimit
import UnforcedLeray.Lib.HeatCylinder.HeatVecL2

/-!
# Part I, `PartI:T02/1/4/4/1/5/1/1/2`: decomposition of `SmoothTensorHeatIsVecHeat`

Source of record: `the November 2 reference manuscript`, lines 3594-3625
(smooth tensors first; Gaussian integration by parts, then the heat semigroup on `H^3`).

The statement `SmoothTensorHeatIsVecHeat` follows from five facts about a smooth cylinder tensor
`S : Plane → Plane × Plane` (take `S x = tensorToPlaneCLE (T x)`):

* `SmoothRowDivHeatPointwise`: `heatDiv θ S = heat θ (rowDivergence S)` pointwise
  (Gaussian integration by parts, source 3594-3625; follows from `NeedSmoothRowIBP`);
* `RowDivPeriodicMemLp`: the row divergence of a smooth cylinder tensor is periodic, measurable and
  square integrable on the normalized cell;
* `HeatDivH3NormalizedAe`: the normalized value of `heatDivH3 S` is a.e. the Gaussian `heatDiv`;
* `NormalizedValueOfAe`: if the centered value of `X ∈ H^3` is a.e. a periodic `f`, the normalized
  value of `X` is a.e. `f`;
* `HeatVecL2Periodic`: the vector heat operator on `L²` of the normalized cell acts on a periodic
  `L²` representative as the Gaussian convolution.
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

/-- **Row-divergence heat, pointwise**, source 3594-3625: for a smooth cylinder tensor `S` and
`θ > 0` (and period `c > 0`: for `c = 0` smooth tensors may be unbounded), the Gaussian `heatDiv θ S` equals the Gaussian heat of the row divergence of `S`
(integration by parts against the Gaussian; `NeedSmoothRowIBP` twice). -/
def SmoothRowDivHeatPointwise : Prop :=
  ∀ (c θ : ℝ), 0 < c → 0 < θ → ∀ (S : Plane → Plane × Plane), Sob.IsCylSmooth c S →
    ∀ z : Plane,
    UnforcedLeray.B0296.heatDiv θ S z =
      UnforcedLeray.B0284.heat θ (rowDivergence S) z

/-- **Row divergence is a periodic `L²` field**, source 3594-3625: for a smooth cylinder tensor `S`
(smooth, `q`-periodic with period `c`, all derivatives bounded), `rowDivergence S` is
`q`-periodic, continuous, and its `Vec`-coordinates are in `L²` of the normalized cell. -/
def RowDivPeriodicMemLp : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (S : Plane → Plane × Plane), Sob.IsCylSmooth c S →
    UnforcedLeray.B0284.IsQPeriodic c (rowDivergence S) ∧ Continuous (rowDivergence S) ∧
      MemLp (fun z => toVec (rowDivergence S z)) 2 (UnforcedLeray.B0284.cellMeasure c)

/-- **Normalized value of `heatDivH3`**, source 3594-3625: for a smooth cylinder tensor `S` the
normalized value of the `H^3` class `heatDivH3 S` is a.e. `toVec (heatDiv θ S)`
(`vectorH3NormalizedValue_heatDivH3` with `heatDivVecL2CLM_apply_to_periodic`). -/
def HeatDivH3NormalizedAe : Prop :=
  ∀ (c θ : ℝ) (hc : 0 < c) (hθ : 0 < θ) (S : Plane → Plane × Plane) (hS : Sob.IsCylSmooth c S),
    (vectorH3NormalizedValue hc (heatDivH3 hc hθ hS) : Plane → Vec) =ᵐ[
        UnforcedLeray.B0284.cellMeasure c]
      fun z => toVec (UnforcedLeray.B0296.heatDiv θ S z)

/-- **Normalized value from the centered value**, source 3594-3625: if the centered-cell value of
`X ∈ H^3` is a.e. a `q`-periodic continuous `f`, then the normalized value of `X` is a.e. `f` on the
normalized cell (`vectorH3PeriodicValueRep` is the periodic extension of the value). -/
def NormalizedValueOfAe : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (X : Cyl.H ℝ Cyl.Vec2 c 0 3) (f : Plane → Vec),
    UnforcedLeray.B0284.IsQPeriodic c f → Continuous f →
    (hVal X =ᵐ[Cyl.cellμ c] f) →
    (vectorH3NormalizedValue hc X : Plane → Vec) =ᵐ[UnforcedLeray.B0284.cellMeasure c] f

/-- **Vector heat on a periodic `L²` field**, source 3594-3625: for a periodic continuous
`R : Plane → Plane` whose `Vec`-coordinates are in `L²` of the normalized cell, `heatVecL2CLM`
sends that class to the class of `toVec (heat θ R)` (the vector form of the periodic action of
`heatL2CLM`, cf. `heatDivVecL2CLM_apply_to_periodic`). -/
def HeatVecL2Periodic : Prop :=
  ∀ (c θ : ℝ) (hc : 0 < c), 0 < θ → ∀ (R : Plane → Plane),
    UnforcedLeray.B0284.IsQPeriodic c R → Continuous R →
    ∀ hmem : MemLp (fun z => toVec (R z)) 2 (UnforcedLeray.B0284.cellMeasure c),
      ∃ hh : MemLp (fun z => toVec (UnforcedLeray.B0284.heat θ R z)) 2
          (UnforcedLeray.B0284.cellMeasure c),
        heatVecL2CLM hc θ (hmem.toLp (fun z => toVec (R z))) =
          hh.toLp (fun z => toVec (UnforcedLeray.B0284.heat θ R z))

theorem smoothTensorHeatIsVecHeat_of (h1 : SmoothRowDivHeatPointwise)
    (h2 : RowDivPeriodicMemLp) (h3 : HeatDivH3NormalizedAe) (h4 : NormalizedValueOfAe)
    (h5 : HeatVecL2Periodic) : SmoothTensorHeatIsVecHeat := by
  have h1pt := h1
  intro c θ hc hθ T hT X hX
  have key : ∀ (S : Plane → Plane × Plane) (hS : Sob.IsCylSmooth c S),
      (hVal X =ᵐ[Cyl.cellμ c] fun z => toVec (rowDivergence S z)) →
      HeatCylinder.heatDivH3 hc hθ hS = HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc X := by
    intro S hS hX
    obtain ⟨hper, hcont, hmem⟩ := h2 c hc S hS
    obtain ⟨hh, hheat⟩ := h5 c θ hc hθ (rowDivergence S) hper hcont hmem
    rw [heatVecH3Semigroup_apply_of_pos hc hθ]
    apply vectorH3NormalizedValue_injective hc
    rw [actualHeatVecH3CLM_apply, vectorH3NormalizedValue_actualHeatVecH3 hc hθ]
    have hXn := h4 c hc X (fun z => toVec (rowDivergence S z))
      (fun z => by simp only [hper z]) (Train.toVecL.continuous.comp hcont) hX
    have hX' : vectorH3NormalizedValue hc X = hmem.toLp (fun z => toVec (rowDivergence S z)) := by
      apply Lp.ext
      filter_upwards [hXn, hmem.coeFn_toLp] with z h1 h2
      rw [h1, h2]
    rw [hX', hheat]
    apply Lp.ext
    filter_upwards [h3 c θ hc hθ S hS, hh.coeFn_toLp] with z h1 h2
    refine h1.trans ?_
    rw [h1pt c θ hc hθ S hS z]
    exact h2.symm

  exact key _ (HeatCylinder.isCylSmooth_postcomp_clm hT tensorToPlaneCLE.toContinuousLinearMap) hX

end UnforcedLeray.Short.PartI
