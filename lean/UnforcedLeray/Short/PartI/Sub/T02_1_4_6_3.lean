import UnforcedLeray.Short.PartI.Sub.T02_1_4_6
import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Operator
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3DerivativeTransport
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3DerivativeComponents
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3P0Compatibility
import UnforcedLeray.Lib.HeatCylinder.CenteredHeatProjectionConditional
import UnforcedLeray.Lib.HeatCylinder.HeatVecCenteredSelfAdjoint

/-!
# Part I, task `PartI:T02/1/4/6/3`: the seed generator (conditional decomposition)

Source of record: `the November 2 reference manuscript`, lines 261-288 (the
heat-generator step for the seed in Gallay-Slijepcevic 2015, Theorem 1.1 and Remark 1.3(2)).

Target: `SeedGenerator` (`Short/PartI/Sub/T02_1_4_6.lean`): for `τ > 0` the seed
`τ ↦ V₀ (P₀ e^{ντΔ} d)` paired with weakly solenoidal `L²` classes `ψL` of `ψ` and `ψ'L` of `Δψ`
(`ψ` a smooth periodic `η`-compact test) has derivative `ν ⟨V₀ (P₀ e^{ντΔ} d), ψ'L⟩`.

**Reduction.**  The Leray projection drops against weakly solenoidal classes
(`TrainB.inner_vecH3P0_eq_of_divFree`), the zero-order class of the heat orbit of the datum class
`x₀` is `e^{ντΔ} x₀` (`centeredHeatVecL2CLM`), and the centered heat is self-adjoint
(`inner_centeredHeatVecL2CLM_symm`), so for `τ > 0`
`⟨V₀ u(τ), ψL⟩ = ⟨x₀, e^{ντΔ} ψL⟩` and `d/dτ` of this is `ν ⟨x₀, e^{ντΔ} ψ'L⟩ = ν ⟨V₀ u(τ), ψ'L⟩`
by the single analytic input `CenteredHeatAgeDerivative` (leaf 2 of `PartI:T02/1/4/6/4`, task
`PartI:T02/1/4/6/4/2`, defined in `Short/PartI/Sub/T02_1_4_6_4.lean`; it is stated for an arbitrary
`L²` class `G`, so it applies with `G = x₀`).  The seed generator therefore adds no new analytic
leaf: it is `seedGenerator_of centeredHeatAgeDerivative`.

`seedGenerator_of` is proved below, with no unproved placeholder and no added axiom.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-! ### Step 1: the zero-order class of the projected seed -/

/-- The centered derivative class equals the centered-cell derivative.  A copy of the private
lemma `centeredVecH3DerivativeClass_eq_vecH3CellDerivCLM_local`
(`Lib/HeatCylinder/HeatVecH3P0Compatibility.lean:27`). -/
theorem seedGen_centeredVecH3DerivativeClass_eq_cell {c : ℝ} (α : Sob.Idx 2 3)
    (x : Cyl.H ℝ Vec c 0 3) :
    HeatCylinder.centeredVecH3DerivativeClass α x = vecH3CellDerivCLM α x := by
  apply Lp.ext
  have hleft := HeatCylinder.centeredVecH3DerivativeClass_coe_ae α x
  have hMP : MeasurePreserving id (Cyl.cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← HeatCylinder.heatVecH3_measure_eq_cell_deriv c]
    exact MeasurePreserving.id _
  have hright := Lp.coeFn_compMeasurePreserving
    ((Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α) x) hMP
  have hright' : (vecH3CellDerivCLM α x : Plane → Vec) =ᵐ[Cyl.cellμ c]
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α x : Plane → Vec) := by
    change (Lp.compMeasurePreserving id hMP
      ((Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α) x) :
        Lp Vec 2 (Cyl.cellμ c)) =ᵐ[Cyl.cellμ c] _
    simpa using hright
  filter_upwards [hleft, hright'] with z hzleft hzright
  exact hzleft.trans hzright.symm

/-- The public zero-index form of `centeredVecH3Derivative_actualHeatVecH3`, stated on the
centered-cell derivative `vecH3CellDerivCLM`. -/
theorem seedGen_vecH3CellDerivCLM_actualHeatVecH3 {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : Cyl.H ℝ Vec c 0 3) :
    vecH3CellDerivCLM Sob.Idx.zero (HeatCylinder.actualHeatVecH3 hc hθ x) =
      HeatCylinder.centeredHeatVecL2CLM hc θ (vecH3CellDerivCLM Sob.Idx.zero x) := by
  have h1 := seedGen_centeredVecH3DerivativeClass_eq_cell (c := c) Sob.Idx.zero
    (HeatCylinder.actualHeatVecH3 hc hθ x)
  have h2 := seedGen_centeredVecH3DerivativeClass_eq_cell (c := c) Sob.Idx.zero x
  have h3 := HeatCylinder.centeredVecH3Derivative_actualHeatVecH3 hc hθ x Sob.Idx.zero
  rw [← h1, ← h2]
  exact h3

/-- At positive age the projected seed pairs with a weakly solenoidal class as the centered heat
at age `ν τ` of the datum class.  The Leray projection is removed by
`inner_vecH3P0_eq_of_divFree`. -/
theorem seedGen_projectedHeatSeedPath_pairing {c ν τ : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hτ : 0 < τ) (x : VectorH3 c) {ψL : Cyl.L2v c} (hψL : ψL ∈ Cyl.divFree c) :
    inner ℝ (vecH3CellDerivCLM Sob.Idx.zero (projectedHeatSeedPath hc hν x τ)) ψL =
      inner ℝ (HeatCylinder.centeredHeatVecL2CLM hc (ν * τ)
        (vecH3CellDerivCLM Sob.Idx.zero x)) ψL := by
  have hθ : 0 < ν * τ := mul_pos hν hτ
  have hp : projectedHeatSeedPath hc hν x τ =
      P0H3CLM hc (HeatCylinder.actualHeatVecH3 hc hθ x) := by
    show P0H3CLM hc (HeatCylinder.heatVecH3Semigroup (c := c) (θ := max 0 (ν * τ)) hc x) = _
    rw [max_eq_right hθ.le, HeatCylinder.heatVecH3Semigroup_apply_of_pos hc hθ,
      HeatCylinder.actualHeatVecH3CLM_apply]
  rw [hp, inner_vecH3P0_eq_of_divFree hc _ hψL, seedGen_vecH3CellDerivCLM_actualHeatVecH3 hc hθ]

/-! ### Step 2: the seed generator from the age derivative of the centered heat -/

/-- **The seed generator from the age derivative of the centered heat.**  `SeedGenerator` follows
from `CenteredHeatAgeDerivative` (leaf 2 of `PartI:T02/1/4/6/4`) applied with `G` the class of the
projected initial datum, the self-adjointness of the centered heat, and the chain rule for
`τ ↦ ν τ`. -/
theorem seedGenerator_of (h : CenteredHeatAgeDerivative) : SeedGenerator := by
  intro ν c hν hc ψ ψL ψ'L hψ hψL hψ'L hψLd hψ'Ld t ht
  set x0 : Cyl.L2v c := vecH3CellDerivCLM Sob.Idx.zero (projectedInitialDatumH3 hc) with hx0
  have hF := h c hc ψ ψL ψ'L hψ hψL hψ'L x0 (ν * t) (mul_pos hν ht)
  have hlin : HasDerivAt (fun τ : ℝ => ν * τ) ν t := by
    simpa using (hasDerivAt_id t).const_mul ν
  have hcomp := hF.comp t hlin
  have hcongr : (fun τ : ℝ => inner ℝ (vecH3CellDerivCLM Sob.Idx.zero
      (projectedHeatSeedPath hc hν (projectedInitialDatumH3 hc) τ)) ψL) =ᶠ[𝓝 t]
      ((fun s : ℝ => inner ℝ x0 (HeatCylinder.centeredHeatVecL2CLM hc s ψL)) ∘
        (fun τ : ℝ => ν * τ)) := by
    filter_upwards [Ioi_mem_nhds ht] with τ hτ
    have hτ' : 0 < τ := Set.mem_Ioi.mp hτ
    rw [seedGen_projectedHeatSeedPath_pairing hc hν hτ' _ hψLd]
    exact HeatCylinder.inner_centeredHeatVecL2CLM_symm hc (mul_pos hν hτ').le x0 ψL
  refine (hcomp.congr_of_eventuallyEq hcongr).congr_deriv ?_
  rw [seedGen_projectedHeatSeedPath_pairing hc hν ht _ hψ'Ld,
    HeatCylinder.inner_centeredHeatVecL2CLM_symm hc (mul_pos hν ht).le x0 ψ'L]
  exact mul_comm _ _

end UnforcedLeray.Short.PartI
