import UnforcedLeray.Short.PartI.Sub.T02
import UnforcedLeray.Lib.TrainB.P0MildLiteralNSInterfaces
import UnforcedLeray.Lib.TrainB.P0SmoothH3

/-!
# Part I, task `PartI:T02/1`: from the mild `H³` solution to a classical solution (conditional)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1, local part: a unique mild solution in BUC, smooth for
positive time; here the datum is `trainDatum c = Train.datum c`).

The target is `LocalClassicalBounded` (`Short/PartI/Sub/T02.lean`).  The route, in the language of
the library (the compact mild `H³` solution of `Lib/TrainB/P0CompactMildTrain.lean`, which is an
abstract `H³(cell)`-valued path), is cut into six `Prop`s:

1. `MildTrainExists`: the library mild solution `u ∈ C([0,T], VectorH3 c)` with the projected
   datum as initial trace (`IsMildTrain`).  Library assembly
   (`exists_uniform_short_projected_NS_mild_train_on_P0_ball_allComponentsDivFree` at
   `x = projectedInitialDatumH3 hc`).
2. `HkPersistence`: the same `u` lies in `C([0,T], H^{k+3})` for every `k`, on the same `[0,T]`
   (the datum `trainDatum c` lies in every `H^k`; `H^k` energy estimate with the `W^{1,∞}` norm of
   `u`, which is controlled by the `H³` norm on `[0,T]`).
3. `SpatialRepFromPersistent`: a spatially smooth periodic representative `w(s)` of `u(s)` with all
   spatial derivatives bounded uniformly on `[0,T]` and jointly continuous (Sobolev embedding on
   the cell, `Lib/SobolevC`).
4. `TimeSmoothLeray`: `w` is jointly `C^∞` up to `s = 0`, solenoidal, has datum `trainDatum c`,
   finite energy, and solves the Navier-Stokes system modulo gradients (the Leray form of the mild
   equation: `∂ₛw = νΔw - P(w·∇w)`; mild ⇒ weak NS,
   `Lib/TrainB/P0MildWeakSpatialPairing.lean`, `P0MildTimeIntegratedPairing.lean`).
5. `LerayVelocityToClassical`: a smooth periodic velocity whose force is `L²`-orthogonal to
   compactly supported periodic solenoidal fields has a smooth periodic pressure.
6. `FiniteEnergyDecay`: periodic, Lipschitz and square integrable on the cell implies decay in
   `|η|` (elementary).

`localClassicalBounded_of` derives `LocalClassicalBounded` from these six.  The unconditional
statement is task `PartI:T02/1` (`Short/PartI/Sub/T02/LocalClassicalBounded.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.B0140 (trainDatum)
open UnforcedLeray.TrainB

/-- **The compact mild `H³` solution** for the datum `trainDatum c` (library objects of
`Lib/TrainB`): a continuous path `u : [0,T] → VectorH3 c` that is a fixed point of
`seed + projectedNonlinearDuhamelCompactMap`, stays in the `P₀` (Leray) range, and has the
projected datum as trace at time `0` (source lines 261-285). -/
def IsMildTrain (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) : Prop :=
  u = ((projectedHeatSeedPath hc hν (projectedInitialDatumH3 hc)).comp compactTimeInclusion) +
      projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u ∧
    (∀ t, P0H3CLM hc (u t) = u t) ∧
    u (compactEvolutionZero hT) = projectedInitialDatumH3 hc

/-- `u` lifts to `C([0,T], H^{k+3})` for every `k`, compatibly with the restriction maps. -/
def PersistentFamily (c T : ℝ) (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) : Prop :=
  ∀ k : ℕ, ∃ uk : ContinuousMap (Icc (0 : ℝ) T) (Cyl.H ℝ Cyl.Vec2 c 0 (k + 3)),
    ∀ t, Sob.W.restrict (Nat.le_add_left 3 k) (uk t) = u t

/-- `w(s)` is a smooth periodic representative of the `H³` element `u(s)` (all its derivative
words `α` of length `≤ 3` agree a.e. on the cell), all spatial derivatives are bounded uniformly
in `s ∈ [0,T]`, and they are jointly continuous in `(s, z)`. -/
structure IsSpatialRepOn (c T : ℝ) (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (w : ℝ → Plane → Vec) : Prop where
  smooth : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (w s)
  periodic : ∀ s ∈ Icc 0 T, Cyl.IsPeriodic c (w s)
  represents : ∀ (s : Icc (0 : ℝ) T) (α : Sob.Idx 2 3),
    (vecH3CellDerivCLM α (u s) : Plane → Vec) =ᵐ[Cyl.cellμ c]
      Sob.iterD ((Sob.cylinder c).word α) (w s)
  bounded : HasBoundedDerivsOn T w
  cont : ∀ k : ℕ, ContinuousOn (fun x : ℝ × Plane => iteratedFDeriv ℝ k (w x.1) x.2)
    (Icc 0 T ×ˢ univ)

/-- A velocity field solving the Navier-Stokes system modulo gradients on `[0,T]`: smooth up to
`s = 0`, periodic, solenoidal, with datum `trainDatum c`, finite energy and bounded spatial
derivatives, and such that for `0 < s < T` the force `∂ₛv + v·∇v - νΔv` (the momentum residual
with the zero pressure) is `L²(cell)`-orthogonal to every smooth `c`-periodic solenoidal field
that vanishes for `|η|` large. -/
structure IsLerayVelocityOn (ν c T : ℝ) (v : ℝ → Plane → Vec) : Prop where
  smooth_v : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ univ)
  periodic_v : ∀ s ∈ Icc 0 T, Cyl.IsPeriodic c (v s)
  solenoidal : ∀ s ∈ Icc 0 T, ∀ z, Cyl.divergence (v s) z = 0
  initial : v 0 = trainDatum c
  finite_energy : ∀ s ∈ Icc 0 T, IntegrableOn (fun z => ‖v s z‖ ^ 2) (Cyl.cell c)
  bounded : HasBoundedDerivsOn T v
  leray : ∀ s ∈ Ioo 0 T, ∀ φ : Plane → Vec, ContDiff ℝ ∞ φ → Cyl.IsPeriodic c φ →
    (∀ z, Cyl.divergence φ z = 0) → (∃ R : ℝ, ∀ z : Plane, R < |z.2| → φ z = 0) →
    ∫ z in Cyl.cell c, inner ℝ (Train.momentumResidual ν v (fun _ _ => (0 : ℝ)) s z) (φ z) = 0

/-! ### The six leaf statements -/

/-- **Step 1** (library assembly, source lines 261-285): for `ν > 0` and `c ≥ 1` the compact mild
`H³` solution exists on some `[0,T]`. -/
def MildTrainExists : Prop :=
  ∀ (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c),
    ∃ (T : ℝ) (hT : 0 < T) (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
      IsMildTrain ν c T hν hc hc1 hT u

/-- **Step 2** (`H^k` persistence on the same `[0,T]`, source lines 261-288): the mild solution
lies in `C([0,T], H^{k+3})` for every `k`. -/
def HkPersistence : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → PersistentFamily c T u

/-- **Step 3** (Sobolev embedding on the cell): a persistent family has a smooth periodic
representative with bounded, jointly continuous spatial derivatives. -/
def SpatialRepFromPersistent : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → PersistentFamily c T u →
    ∃ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w

/-- **Step 4** (time regularity and the Leray form of the equation): the spatial representative
of the mild solution is jointly smooth up to `s = 0` and solves the equation modulo gradients. -/
def TimeSmoothLeray : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    IsLerayVelocityOn ν c T w

/-- **Step 5** (pressure from the Leray form): a velocity solving the system modulo gradients has a
smooth periodic pressure (jointly smooth on `[0,T] × ℝ²`) with the momentum equation for
`0 < s < T`. -/
def LerayVelocityToClassical : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec), 0 < ν → 1 ≤ c → 0 < T → IsLerayVelocityOn ν c T v →
    ∃ p : ℝ → Plane → ℝ,
      ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p x.1 x.2) (Icc 0 T ×ˢ univ) ∧
      (∀ s ∈ Icc 0 T, Cyl.IsPeriodic c (p s)) ∧
      ∀ s ∈ Ioo 0 T, ∀ z, Train.momentumResidual ν v p s z = 0

/-- **Step 6** (decay from finite energy, elementary): a differentiable `c`-periodic field with
bounded first derivative and square integrable on the cell tends to `0` as `|η| → ∞`.  (If
`‖v(q₀,η₀)‖ ≥ ε` with `|η₀|` large, then `‖v‖ ≥ ε/2` on a disc of radius `ε/(2 sup‖Dv‖)`; the discs
for infinitely many far-apart `η₀` give infinite energy on the cell.) -/
def FiniteEnergyDecay : Prop :=
  ∀ (c T : ℝ) (v : ℝ → Plane → Vec), 0 < c → (∀ s ∈ Icc 0 T, Cyl.IsPeriodic c (v s)) →
    (∀ s ∈ Icc 0 T, Differentiable ℝ (v s)) → HasBoundedDerivsOn T v →
    (∀ s ∈ Icc 0 T, IntegrableOn (fun z => ‖v s z‖ ^ 2) (Cyl.cell c)) → VelocityDecayOn T v

/-- **`LocalClassicalBounded` from the six steps.** -/
theorem localClassicalBounded_of (h1 : MildTrainExists) (h2 : HkPersistence)
    (h3 : SpatialRepFromPersistent) (h4 : TimeSmoothLeray) (h5 : LerayVelocityToClassical)
    (h6 : FiniteEnergyDecay) : LocalClassicalBounded := by
  intro ν c hν hc1
  have hc : 0 < c := zero_lt_one.trans_le hc1
  obtain ⟨T, hT, u, hu⟩ := h1 ν c hν hc hc1
  have hk := h2 ν c T hν hc hc1 hT u hu
  obtain ⟨w, hw⟩ := h3 ν c T hν hc hc1 hT u hu hk
  have hL := h4 ν c T hν hc hc1 hT u hu w hw
  obtain ⟨p, hps, hpp, hpm⟩ := h5 ν c T w hν hc1 hT hL
  refine ⟨T, hT, w, p, ?_, hL.bounded, ?_⟩
  · exact
      { smooth_v := hL.smooth_v
        smooth_p := hps
        periodic_v := hL.periodic_v
        periodic_p := hpp
        solenoidal := hL.solenoidal
        momentum := hpm
        initial := hL.initial
        finite_energy := hL.finite_energy }
  · exact h6 c T w hc hL.periodic_v (fun s hs => (hw.smooth s hs).differentiable (by simp))
      hL.bounded hL.finite_energy

end UnforcedLeray.Short.PartI
