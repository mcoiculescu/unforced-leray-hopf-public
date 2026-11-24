import UnforcedLeray.Short.PartI.Sub.T02_1
import UnforcedLeray.Lib.TrainB.P0CompactPathExtension

/-!
# Part I, task `PartI:T02/1/4`: time regularity and the Leray form of the mild equation
(conditional)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1 and Remark 1.3(2): the mild solution is smooth for positive
time and the pressure is recovered from the equation; here the datum `trainDatum c` is smooth,
solenoidal and lies in every `H^k`, so the solution is smooth up to `s = 0` as well).

Target: `TimeSmoothLeray` (`Short/PartI/Sub/T02_1.lean`): for the compact mild `H³` train
solution `u` and a smooth spatial representative `w` (`IsSpatialRepOn`), `w` satisfies
`IsLerayVelocityOn`.  Six of the seven fields of `IsLerayVelocityOn` are cut into leaf `Prop`s
(ids `PartI:T02/1/4/1` ... `/6`); `periodic_v` and `bounded` are the fields of `IsSpatialRepOn`.
Joint smoothness uses the persistence `HkPersistence` (task `PartI:T02/1/2`) as a hypothesis.

* `RepFiniteEnergy`, `RepInitial`, `RepSolenoidal`: the three easy fields; `represents` with
  `α = 0` identifies `w s` with the `L²(cell)` value of `u s`.
* `MildPathTimeSmooth`: the `H^{k+3}`-valued lift of `u` is `C^∞` in time on `[0,T]` (up to the
  end points, one-sided).  Mathematics: `u' = νΔu - P₀(u·∇u)` holds in `H^{m-2}` and the right-hand
  side is as smooth in time as `u` is, with values in every `H^m` (`H^m` is an algebra for `m ≥ 2`,
  `P₀` and `Δ` are bounded between Sobolev spaces); induction on the order of the time derivative.
* `JointSmoothOfHk`: Sobolev embedding on the cell turns `u ∈ C^∞([0,T], H^m)` for all `m` into
  joint smoothness of the representative.
* `RepLeray`: weak-in-time Navier-Stokes identity for the smooth representative, differentiated
  to the pointwise Leray form.
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

/-! ### The leaf statements -/

/-- **Leaf 1** (finite energy; elementary).  `represents` with `α = 0` says that `w s` equals the
`L²(cell)` class `vecH3CellDerivCLM 0 (u s)` almost everywhere on the cell, so `‖w s‖²` is
integrable on the cell. -/
def RepFiniteEnergy : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    ∀ s ∈ Icc (0 : ℝ) T, IntegrableOn (fun z => ‖w s z‖ ^ 2) (Cyl.cell c)

/-- **Leaf 2** (the initial trace; source lines 261-285).  `w 0 = trainDatum c`.  Proof idea:
`represents` at the point `compactEvolutionZero hT` with `α = 0` gives `w 0 =ᵐ` the `L²` value of
`u (compactEvolutionZero hT) = projectedInitialDatumH3 hc`, which is the class of `Train.datum c`
by `projectedInitialDatumH3_value` (`Lib/TrainB/ProjectedInitialDatum.lean`); both `w 0` and
`trainDatum c = Train.datum c` are continuous and `c`-periodic, so a.e. equality on the cell
`[-c/2,c/2) × ℝ` (its interior is open and dense in the cell) gives equality everywhere. -/
def RepInitial : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    w 0 = trainDatum c

/-- **Leaf 3** (solenoidality; source lines 261-288).  `div (w s) = 0` pointwise for every
`s ∈ [0,T]`.  Proof idea: `u s` is `P₀`-fixed, so by `P0H3CLM_value_mem_divFree`
(`Lib/TrainB/P0H3Range.lean`) the value `vecH3CellDerivCLM 0 (u s)` lies in `Cyl.divFree c`, the
weakly solenoidal `L²` fields; `w s` is smooth and agrees with it a.e. (`represents`), so the
weak divergence of `w s` vanishes, i.e. `∫_cell ⟨w s, ∇χ⟩ = 0` for cylinder tests `χ`; integration
by parts on the cell (`Cyl.integral_cell_partialQ_mul`, `Cyl.integral_cell_partialEta_mul`,
`Lib/Cylinder/IBP.lean`) and the fundamental lemma on the cylinder (`Sob.cylinder c`, `ae_zero`)
give `div (w s) = 0` a.e., hence everywhere by continuity (the cell has dense interior and `w s`
is periodic).  Alternatively use the order-one `represents` words
(`vecH3CellDerivCLM α (u s)` for `α` the `q`- and `η`-derivative words) together with the
`H³` definition of `divFree` (`Lib/CylinderB/Leray.lean`). -/
def RepSolenoidal : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    ∀ s ∈ Icc (0 : ℝ) T, ∀ z, Cyl.divergence (w s) z = 0

/-- **Leaf 4** (time smoothness of the mild path in every `H^m`; HEAVY, source lines 261-288).
Every `H^{k+3}`-valued lift `uk` of the mild path `u` is `C^∞` on `[0,T]` as a map of the time
variable (one-sided at `0` and `T`; `extendCompactPath hT.le uk` is the constant-at-the-ends
extension, so `ContDiffOn` on `Icc 0 T` only sees `uk`).  Mathematics: with `g = P₀(u·∇u) ∈
C([0,T], H^{m})` for every `m` (persistence, `HkPersistence`, makes `u ∈ C([0,T], H^m)` for all
`m`; `H^m` is an algebra, `P₀H^m ⊂ H^m` bounded) the mild equation `u = e^{tνΔ}u₀ - ∫ e^{(t-r)νΔ} g`
is the weak solution of `u' = νΔu - g` in `H^{m-2}`, and `νΔu - g ∈ C([0,T], H^{m-2})`, so
`u ∈ C¹([0,T], H^{m-2})` for all `m`; inductively, if `u ∈ C^j([0,T], H^m)` for all `m` then the
right-hand side `νΔu - P₀(u·∇u)` is `C^j([0,T], H^{m-2})` for all `m`, hence `u ∈
C^{j+1}([0,T], H^m)` for all `m`.  The library has the `H³` heat semigroup and `P₀H3CLM` only
(`Lib/HeatCylinder`, `Lib/TrainB`); the `H^m` versions (heat semigroup continuity, `P₀`,
product estimate) are expected to need a further split, as is the `t = 0` end point (the datum
`trainDatum c` lies in every `H^m` and is solenoidal, so `u'(0) = νΔu₀ - P₀(u₀·∇u₀)` is
defined; there is no boundary compatibility condition on the cylinder). -/
def MildPathTimeSmooth : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ k : ℕ,
    ∀ uk : ContinuousMap (Icc (0 : ℝ) T) (Cyl.H ℝ Cyl.Vec2 c 0 (k + 3)),
      (∀ t, Sob.W.restrict (Nat.le_add_left 3 k) (uk t) = u t) →
      ContDiffOn ℝ ∞ (extendCompactPath hT.le uk) (Icc (0 : ℝ) T)

/-- **Leaf 5** (joint smoothness of the representative; HEAVY, Sobolev embedding on the cell).
If for every `k` the `H^{k+3}` lift of `u` exists and is `C^∞` in time, then the spatial
representative `w` is jointly `C^∞` on `[0,T] × ℝ²`.  Proof idea: the Sobolev embedding of
`H^{m+2}(cell)` into `C_b^m` (translation invariant in `η`, hence with a constant independent of
the position; `Lib/SobolevC`, `Lib/Sobolev/Cylinder.lean`) is a continuous linear map, so the
continuous representative of `u_{m+2}(s)` -- which equals `w s` because both are continuous and
agree a.e. -- depends `C^∞` on `s`, with `∂_s^j D^α w (s) = D^α E(∂_s^j u(s))`; these are jointly
continuous in `(s,z)` (uniform in `s` continuity of an element of `C_b^m` plus continuity in `z`),
and a function on the convex set `[0,T] × ℝ²` all of whose mixed partials `∂_s^j D^α` are jointly
continuous is `C^∞` there (induction with `contDiffOn_succ_iff_fderivWithin`). -/
def JointSmoothOfHk : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    (∀ k : ℕ, ∃ uk : ContinuousMap (Icc (0 : ℝ) T) (Cyl.H ℝ Cyl.Vec2 c 0 (k + 3)),
      (∀ t, Sob.W.restrict (Nat.le_add_left 3 k) (uk t) = u t) ∧
      ContDiffOn ℝ ∞ (extendCompactPath hT.le uk) (Icc (0 : ℝ) T)) →
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => w x.1 x.2) (Icc (0 : ℝ) T ×ˢ univ)

/-- **Leaf 6** (the Leray form; HEAVY, source lines 261-288).  For a jointly smooth spatial
representative `w` of the mild path, the force `∂ₛw + w·∇w - νΔw` (momentum residual with zero
pressure) is `L²(cell)`-orthogonal to every smooth periodic solenoidal field with `η`-compact
support, for each `0 < s < T`.  Proof idea: the time-integrated mild pairing
`integral_compact_mild_pairing_time_path` (`Lib/TrainB/P0MildTimeIntegratedPairing.lean`, with
`inner_vecH3_mild_fixedPoint_eq` in `Lib/TrainB/P0MildWeakSpatialPairing.lean`) against the
time-dependent solenoidal test `χ(t) φ` (a continuous `divFree` path) gives
`∫ χ ⟨w(t),φ⟩ = ∫ χ ⟨w(0),φ⟩ - ∫ χ(t) ∫₀ᵗ ⟨stress orbit, φ⟩`; the heat-generator step converts
the stress-orbit term to `∫₀ᵗ ⟨νΔw - w·∇w, φ⟩ ds` (`Lib/HeatCylinder` kernels; this is the step
the library keeps separate), the right-hand side is continuous in `t` (bounded jointly continuous
derivatives of `w`, compact `η`-support of `φ`), so `t ↦ ⟨w(t),φ⟩` is `C¹` with derivative
`⟨νΔw - w·∇w, φ⟩`; on the other hand `w` jointly `C¹` lets one differentiate under the cell
integral (dominated convergence on the compact `η`-support), giving derivative `⟨∂ₛw, φ⟩`.
Subtract.  Expected to need a further split at the heat-generator step. -/
def RepLeray : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => w x.1 x.2) (Icc (0 : ℝ) T ×ˢ univ) →
    ∀ s ∈ Ioo (0 : ℝ) T, ∀ φ : Plane → Vec, ContDiff ℝ ∞ φ → Cyl.IsPeriodic c φ →
      (∀ z, Cyl.divergence φ z = 0) → (∃ R : ℝ, ∀ z : Plane, R < |z.2| → φ z = 0) →
      ∫ z in Cyl.cell c, inner ℝ (Train.momentumResidual ν w (fun _ _ => (0 : ℝ)) s z) (φ z) = 0

/-! ### The conditional theorem -/

/-- **`TimeSmoothLeray` from the persistence and the six leaves.**  `HkPersistence`
(`PartI:T02/1/2`) supplies the `H^{k+3}` lifts, Leaves 4 and 5 give joint smoothness, and the
remaining fields are Leaves 1, 2, 3, 6 and the fields `periodic`, `bounded` of
`IsSpatialRepOn`. -/
theorem timeSmoothLeray_of (hP : HkPersistence) (h1 : RepFiniteEnergy) (h2 : RepInitial)
    (h3 : RepSolenoidal) (h4 : MildPathTimeSmooth) (h5 : JointSmoothOfHk) (h6 : RepLeray) :
    TimeSmoothLeray := by
  intro ν c T hν hc hc1 hT u hu w hw
  have hper := hP ν c T hν hc hc1 hT u hu
  have hsm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => w x.1 x.2) (Icc (0 : ℝ) T ×ˢ univ) := by
    refine h5 ν c T hν hc hc1 hT u hu w hw fun k => ?_
    obtain ⟨uk, huk⟩ := hper k
    exact ⟨uk, huk, h4 ν c T hν hc hc1 hT u hu k uk huk⟩
  exact
    { smooth_v := hsm
      periodic_v := hw.periodic
      solenoidal := h3 ν c T hν hc hc1 hT u hu w hw
      initial := h2 ν c T hν hc hc1 hT u hu w hw
      finite_energy := h1 ν c T hν hc hc1 hT u hu w hw
      bounded := hw.bounded
      leray := h6 ν c T hν hc hc1 hT u hu w hw hsm }

end UnforcedLeray.Short.PartI
