import UnforcedLeray.Short.PartI.Sub.T02_1
import UnforcedLeray.Short.PartI.TrainClass
import UnforcedLeray.Lib.TrainB.P0UniformBallRestart

/-!
# Part I, task `PartI:T04` (organizer design): global continuation of the train — vocabulary

Source of record: `the November 2 reference manuscript`, lines 261-288:
the datum "is divergence free and belongs to `BUC ∩ H^k` for every `k`" (268-269); the
Gallay-Slijepčević theorem "gives a unique global mild solution in `BUC`, smooth for positive
time, with the bounded periodic pressure choice" (270-277); "It is also the finite-energy solution
... which continues `L²` membership.  Approximation and transverse cutoffs then give the velocity
and vorticity energy identities.  The scalar vorticity equation preserves zero circulation and its
`L¹, L^∞` bounds.  Uniqueness gives `v(-q,-η,s) = -v(q,η,s)`" (278-288).

## Route (design of the organizer for `PartI:T04/org`)

The cited global existence is proved by continuation of the library's compact mild `H³`
solution for the datum `trainDatum c`, whose existence time depends only on the `H³` norm of the
restart state (`TrainB.exists_uniform_short_projected_mild_train_on_P0_ball`):

1. `MildConcat`: two compact mild solutions, the second started at the final state of the first,
   concatenate to a compact mild solution on the sum of the intervals (the library restart
   identity `TrainB.compact_mild_restart_equation` read backwards).
2. `MildTrainH3APriori` (proved in `Compose.lean` from 3-5 below and the `PartI:T02/1` chain): the
   `H³` norm of a mild train on `[0,T]` is bounded by a constant depending only on `ν, c, S ≥ T`.
3. `H3NormOfRep`: the `H³` norm of `u(t)` is controlled by the cell `L²` norms of the derivatives
   of order `≤ 3` of its smooth representative.
4. `JetL2FromPersistent`: the representative of a persistent family (`H^{k+3}` for every `k`) has
   every derivative in `L²(cell)`, uniformly on `[0,T]` (the qualitative input that makes the
   transverse cutoffs of lines 285-286 converge).
5. `ClassicalH3APriori` (`APriori.lean`): the energy method of lines 278-288 for classical
   solutions on `[0,T]` with the datum `trainDatum c`.
6. `TrainOnUnique`: two bounded classical trains agree on their common interval (uniqueness,
   line 288, plus the decaying pressure gauge and the decaying stream).

`Compose.lean` derives `MildTrainGlobal` (mild trains on every `[0,S]`), then the classical train
on every `[0,S]` (the `PartI:T02` chain applies verbatim on `[0,S]`), then glues them into a global
`B0140.TrainSol` of the class `IsBUCTrain`, which is `TrainGlobalExistence`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.B0140 (trainDatum)
open UnforcedLeray.TrainB

/-! ### Cell `L²` norms of jets -/

/-- `‖D^j v(s)‖²_{L²(cell)}`: the unnormalized cell integral (line 254) of the squared operator
norm of the `j`-th spatial derivative of the velocity at age `s`. -/
def velJet (c : ℝ) (j : ℕ) (v : ℝ → Plane → Vec) (s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j (v s) z‖ ^ 2

/-- `‖D^j ω(s)‖²_{L²(cell)}` for the scalar vorticity `ω(s) = curl v(s)` (line 286). -/
def vortJet (c : ℝ) (j : ℕ) (v : ℝ → Plane → Vec) (s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j (Cyl.curl (v s)) z‖ ^ 2

/-- **Qualitative `H^∞` on `[0,T]`** (lines 268-269 and 285: the datum is in every `H^k` and the
solution "continues `L²` membership"): every spatial derivative of `v(s)` is square integrable on
the cell, with a bound uniform in `s ∈ [0,T]`.  Integrability is part of the statement, so no
Bochner junk value enters `velJet`. -/
def JetL2On (c T : ℝ) (v : ℝ → Plane → Vec) : Prop :=
  ∀ j : ℕ, ∃ K : ℝ, ∀ s ∈ Icc (0 : ℝ) T,
    IntegrableOn (fun z => ‖iteratedFDeriv ℝ j (v s) z‖ ^ 2) (Cyl.cell c) ∧ velJet c j v s ≤ K

/-- **The class of the a priori estimates**: a classical solution on `[0,T]` with the datum
`trainDatum c` (`IsClassicalOn`, `Sub/T02.lean`), all spatial derivatives bounded, the decaying
pressure gauge (line 447), and every derivative in `L²(cell)` uniformly on `[0,T]`.  The
classical solution produced from a mild train by the `PartI:T02/1` chain is in this class
(`Compose.lean`). -/
structure IsAPrioriClass (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) : Prop where
  pos : 0 < T
  classical : IsClassicalOn ν c T v p
  bounded : HasBoundedDerivsOn T v
  pressure_decay : PressureDecayOn T p
  jet_l2 : JetL2On c T v

/-! ### Leaf statements (mild level and bridges) -/

/-- **Concatenation of compact mild solutions** (lines 276-277, the mild solution; the restart
identity `TrainB.compact_mild_restart_equation` read backwards).  Let `u₁` be a compact mild
solution on `[0,T₁]` from the `P₀`-fixed state `x` (fixed point of the projected heat seed of `x`
plus the projected nonlinear Duhamel term, `P₀`-fixed, trace `x`), and `u₂` a compact mild solution
on `[0,T₂]` from the final state `u₁(T₁)`.  Then there is a compact mild solution on `[0,T₁+T₂]`
from `x` (in fact `u(t) = u₁(t)` for `t ≤ T₁`, `u(t) = u₂(t - T₁)` for `t ≥ T₁`). -/
def MildConcat : Prop :=
  ∀ (ν c T₁ T₂ : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (x : VectorH3 c) (u₁ : ContinuousMap (Icc (0 : ℝ) T₁) (VectorH3 c))
    (u₂ : ContinuousMap (Icc (0 : ℝ) T₂) (VectorH3 c)),
    P0H3CLM hc x = x →
    u₁ = (projectedHeatSeedPath hc hν x).comp compactTimeInclusion +
      projectedNonlinearDuhamelCompactMap hc hc1 hν hT₁.le u₁ →
    (∀ t, P0H3CLM hc (u₁ t) = u₁ t) →
    u₁ (compactEvolutionZero hT₁) = x →
    u₂ = (projectedHeatSeedPath hc hν (u₁ ⟨T₁, hT₁.le, le_rfl⟩)).comp compactTimeInclusion +
      projectedNonlinearDuhamelCompactMap hc hc1 hν hT₂.le u₂ →
    (∀ t, P0H3CLM hc (u₂ t) = u₂ t) →
    u₂ (compactEvolutionZero hT₂) = u₁ ⟨T₁, hT₁.le, le_rfl⟩ →
    ∃ u : ContinuousMap (Icc (0 : ℝ) (T₁ + T₂)) (VectorH3 c),
      u = (projectedHeatSeedPath hc hν x).comp compactTimeInclusion +
        projectedNonlinearDuhamelCompactMap hc hc1 hν (add_pos hT₁ hT₂).le u ∧
      (∀ t, P0H3CLM hc (u t) = u t) ∧
      u (compactEvolutionZero (add_pos hT₁ hT₂)) = x

/-- **The `H³` norm through the smooth representative** (cell norms unnormalized, line 254):
`‖u(t)‖²_{H³} = Σ_{|α| ≤ 3} ‖∂^α u(t)‖²_{L²(cell)}` (`Sob.W.norm_sq`), each weak derivative is
represented by the classical derivative word of `w(t)` (`IsSpatialRepOn.represents`), and a word
of length `j` along the unit directions is bounded by `‖D^j w(t)‖`.  So a common bound `B` of the
cell norms of `D^j w(s)`, `j ≤ 3`, bounds `‖u(t)‖²` by a universal multiple of `B`. -/
def H3NormOfRep : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (c T : ℝ) (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (w : ℝ → Plane → Vec) (B : ℝ), 0 < c → IsSpatialRepOn c T u w →
    (∀ s ∈ Icc (0 : ℝ) T, ∀ j : ℕ, j ≤ 3 →
      IntegrableOn (fun z => ‖iteratedFDeriv ℝ j (w s) z‖ ^ 2) (Cyl.cell c) ∧
        velJet c j w s ≤ B) →
    ∀ t, ‖u t‖ ^ 2 ≤ K * B

/-- **All derivatives of the representative are in `L²(cell)`** (lines 268-269, 285): if `u` lifts
to `C([0,T], H^{k+3})` for every `k` (`PersistentFamily`) and `w` is its smooth representative,
then `w(s)` is the continuous representative of `u_k(s) ∈ H^{k+3}` (`cylSobolevRep`, uniqueness
`aePeriodicEq`), so every derivative of `w(s)` is square integrable with the bound
`C_j sup_{[0,T]} ‖u_k‖`. -/
def JetL2FromPersistent : Prop :=
  ∀ (c T : ℝ) (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) (w : ℝ → Plane → Vec),
    0 < c → 1 ≤ c → 0 < T → PersistentFamily c T u → IsSpatialRepOn c T u w → JetL2On c T w

/-- **Bounded classical trains agree on their common interval** (line 276, "unique"; line 288,
"Uniqueness"; the decaying pressure gauge, line 447; the stream is fixed by `v = ∇^⊥ψ` and
`ψ → 0`).  Velocity: `classicalUniquenessBounded`
(`Tasks/ClassicalOdd/ClassicalUniquenessBounded.lean`) on `[0, min S S']`.  Pressure: equal
momentum residuals give equal gradients, and two decaying pressures with equal gradients are equal
(for `0 < s < min S S'`; the endpoints by continuity in `s`).  Stream: equal perpendicular
gradients and decay. -/
def TrainOnUnique : Prop :=
  ∀ (ν c S S' : ℝ) (v v' : ℝ → Plane → Vec) (p p' ψ ψ' : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    0 < S → 0 < S' → IsTrainOn ν c S v p ψ → IsTrainOn ν c S' v' p' ψ' →
    HasBoundedDerivsOn S v → HasBoundedDerivsOn S' v' →
    ∀ s : ℝ, 0 ≤ s → s ≤ S → s ≤ S' → v s = v' s ∧ p s = p' s ∧ ψ s = ψ' s

/-! ### Intermediate statements (proved in `Compose.lean`) -/

/-- A compact mild train (`IsMildTrain`, `Sub/T02_1.lean`) exists on `[0,T]`. -/
def MildTrainOn (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) : Prop :=
  ∃ (hT : 0 < T) (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)), IsMildTrain ν c T hν hc hc1 hT u

/-- **A priori `H³` bound for mild trains**: on `[0,T]` with `T ≤ S` the `H³` norm of a mild train
is bounded by a constant depending only on `ν, c, S`. -/
def MildTrainH3APriori : Prop :=
  ∀ (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (S : ℝ), 0 < S →
    ∃ M : ℝ, ∀ (T : ℝ) (hT : 0 < T), T ≤ S → ∀ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
      IsMildTrain ν c T hν hc hc1 hT u → ∀ t, ‖u t‖ ≤ M

/-- **The global mild train** (lines 276-277: "a unique global mild solution"): a compact mild
train exists on every `[0,S]`. -/
def MildTrainGlobal : Prop :=
  ∀ (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (S : ℝ) (hS : 0 < S),
    ∃ u : ContinuousMap (Icc (0 : ℝ) S) (VectorH3 c), IsMildTrain ν c S hν hc hc1 hS u

/-- The bounded classical train exists on every finite interval `[0,S]`. -/
def TrainClassicalOnEvery : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ S : ℝ, 0 < S →
    ∃ (v : ℝ → Plane → Vec) (p ψ : ℝ → Plane → ℝ), IsTrainOn ν c S v p ψ ∧ HasBoundedDerivsOn S v

end UnforcedLeray.Short.PartI
