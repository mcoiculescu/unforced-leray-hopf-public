import UnforcedLeray.Short.PartI.Sub.T02_1_2

/-!
# Part I, task `PartI:T02/1/2/2`: `SeedDerivative` (conditional)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1: the datum is in `H^k` for every `k` and the Gaussian heat
orbit commutes with the horizontal derivatives).

The target is `SeedDerivative` (`Short/PartI/Sub/T02_1_2.lean`): if `x' = ∂_j x` weakly in
`H³`, then `t ↦ P₀ e^{νtΔ} x'` is the `∂_j`-derivative path of `t ↦ P₀ e^{νtΔ} x`.

## Decomposition

`seedPath T hc hν x t = P₀H3CLM hc (heatVecH3Semigroup (θ := max 0 (ν t)) hc x)`
(`projectedHeatSeedPath`, `Lib/TrainB/P0ArbitraryInitialLocalMild.lean:15`), so `SeedDerivative`
is the composition of two commutation statements, each for a *single* operator:

* `HeatWeakDeriv`: `heatVecH3Semigroup θ` (identity for `θ ≤ 0`, the actual Gaussian heat for
  `θ > 0`) preserves the relation "`x'` is the weak `∂_j`-derivative of `x`".
* `P0WeakDeriv`: `P0H3CLM` preserves the same relation.

Both are proved from one bridge, `WeakDerivCell`: on `H³` the relation
`HasWeakDeriv [∂_j] (val x) (val x')` is the equality of the two `L²`-cell classes
`vecH3CellDerivCLM (∂_j) x = vecH3CellDerivCLM zero x'`.

`seedDerivative_of` (compiled here) is the assembly.  No `sorry`, `admit`, `axiom` or
`native_decide`.
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

/-- **Leaf L1** (bridge between the weak-derivative relation and `L²`-cell classes; source lines
261-288, definition of `H^3` via weak derivatives).  For `x, x' ∈ H³`, `x'` is the periodic weak
`∂_j`-derivative of `x` iff the `∂_j` component of `x` and the value component of `x'` have the
same `L²`-cell class (`vecH3CellDerivCLM α` is the `α` derivative component of an `H³` element
read in `L²(cell)`, `Lib/TrainB/P0SmoothH3.lean:68`; `Sob.Idx.cons j Sob.Idx.zero` is the
first-order index `∂_j`, `Cyl.H.iQ`/`iEta` for `j = 0`/`1`).  Proof: `Sob.W.hasWeakDeriv x
(Sob.Idx.cons j Sob.Idx.zero)` with `Sob.TestDomain.word_cons`/`word_zero`,
`HasWeakDeriv.ae_unique` and `HasWeakDeriv.congr_ae` (`Lib/Sobolev/WeakDeriv.lean`),
`Sob.W.deriv_zero`, `Sob.ae_eq_wμ_iff`, injectivity of `weightedToCellL2Isometry`. -/
def WeakDerivCell : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (j : Fin 2) (x x' : VectorH3 c),
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val x : Plane → Vec) (Cyl.H.val x' : Plane → Vec) ↔
    vecH3CellDerivCLM (Sob.Idx.cons j Sob.Idx.zero : Sob.Idx 2 3) x =
      vecH3CellDerivCLM (Sob.Idx.zero : Sob.Idx 2 3) x'

/-- **Leaf H** (the `H³` Gaussian heat commutes with `∂_j`; source lines 261-288).  If `x'` is the
weak `∂_j`-derivative of `x` in `H³`, then for every age `θ` (the identity for `θ ≤ 0`)
`e^{θΔ} x'` is the weak `∂_j`-derivative of `e^{θΔ} x`.  Library:
`HeatCylinder.centeredVecH3Derivative_actualHeatVecH3`
(`Lib/HeatCylinder/HeatVecH3P0Compatibility.lean:60`: the `α` component of the actual `H³` heat is
the centered `L²` heat of the `α` component), `heatVecH3Semigroup_apply_of_pos`,
`heatVecH3Semigroup_eq_id_of_nonpos`; the cell classes are linked to `vecH3CellDerivCLM` by
`centeredVecH3DerivativeClass_eq_vecH3CellDerivCLM_local` (private in that file, re-prove). -/
def HeatWeakDeriv : Prop :=
  ∀ (c θ : ℝ) (hc : 0 < c) (j : Fin 2) (x x' : VectorH3 c),
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val x : Plane → Vec) (Cyl.H.val x' : Plane → Vec) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc x) : Plane → Vec)
      (Cyl.H.val (HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc x') : Plane → Vec)

/-- **Leaf P** (the `H³` Leray projection commutes with `∂_j`; source lines 261-288).  If `y'` is
the weak `∂_j`-derivative of `y` in `H³`, then `P₀ y'` is the weak `∂_j`-derivative of `P₀ y`.
Library: `TrainB.P0H3CLM_apply_component`
(`vecH3CellDerivCLM α (P0H3CLM hc y) = Cyl.P0 c (vecH3CellDerivCLM α y)`,
`Lib/TrainB/P0H3Operator.lean:71`). -/
def P0WeakDeriv : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (j : Fin 2) (y y' : VectorH3 c),
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val y : Plane → Vec) (Cyl.H.val y' : Plane → Vec) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (P0H3CLM hc y) : Plane → Vec) (Cyl.H.val (P0H3CLM hc y') : Plane → Vec)

/-- **`SeedDerivative` from the heat and the projection commutation.**  The seed path at time `t`
is `P₀ e^{max 0 (ν t) Δ} x`, so the two leaves apply one after the other. -/
theorem seedDerivative_of (hH : HeatWeakDeriv) (hP : P0WeakDeriv) : SeedDerivative := by
  intro ν c T hν hc j x x' h t
  exact hP c hc j _ _ (hH c (max 0 (ν * (t : ℝ))) hc j x x' h)

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.seedDerivative_of
