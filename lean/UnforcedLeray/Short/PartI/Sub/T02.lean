import UnforcedLeray.Units.B0140

/-!
# Part I, task `PartI:T02`: the local classical train (conditional)

Source of record: `the November 2 reference manuscript`, lines 261-288
(the exact cylinder Navier-Stokes solution with initial stream `ψ(q,η,0) = Σₙ -2 e^{-((q-nc)²+η²)/4}`;
Gallay-Slijepcevic 2015, Theorem 1.1 and Remark 1.3(2): "a unique global mild solution in BUC,
smooth for positive time, with the bounded periodic pressure choice"; "Uniqueness gives
`v(-q,-η,s) = -v(q,η,s)`"), and lines 394-450 (the decaying pressure gauge).

## What is proved here

`IsTrainOn ν c T v p ψ` is `B0140.IsTrain` restricted to `[0, T]` (same fields; `momentum` on
`(0, T)`); `isTrainOn_of_isTrain` shows that a global train restricts to it.  The original target of


The local statement is split along the construction into five `Prop`s, each a true classical or
mild statement about the datum `trainDatum c`:

1. `LocalClassicalBounded`: the compact mild `H³` solution on `[0,T]`
   (`Lib/TrainB/P0CompactMildTrain.lean`, `P0GlobalSeedMild.lean`) is a classical solution, smooth up
   to `s = 0` (parabolic bootstrap, datum in every `H^k`), with all spatial derivatives bounded and
   the velocity decaying in `|η|` (`BUC ∩ L²`).
2. `LerayPressureGauge`: a classical pressure can be changed by a function of `s` so that it
   decays as `|η| → ∞` (line 447, "the decaying pressure gauge").
3. `ClassicalOdd`: uniqueness (energy method on the cell, pressure decaying) applied to the
   reflected pair `(-v(s,-z), p(s,-z))`, whose datum is the same because `trainDatum` is odd
   (`B0140.trainDatum_neg`), gives `v(s,-z) = -v(s,z)`.
4. `VorticityFirstMoment`: `∫_cell (1 + |η|) |ω(s)| < ∞` (the vorticity equation with the weight
   `1 + |η|`, Gronwall; the datum vorticity has Gaussian tails).
5. `StreamExists`: for an odd classical field with that vorticity moment, `v = ∇^⊥ψ` with `ψ`
   differentiable and `ψ → 0` as `|η| → ∞` (cylinder Biot-Savart: zero circulation by periodicity
   and decay, vanishing first moment and zero horizontal flux by oddness).

`train_local_classical_of` derives `TrainLocalClassical` from these five.  The unconditional target
is task `PartI:T02` (`Short/PartI/Tasks/TrainLocalClassical.lean`).  Tasks `PartI:T03` and
`PartI:T04` (classical train on `[0,T)`, vorticity bounds, global continuation) should use
`IsTrainOn` and `IsClassicalOn` from this file.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.GaussianVortex (perpendicularGradient)
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.B0140 (trainDatum)

/-- A classical solution of the cylinder Navier-Stokes system on `[0,T]`: the fields of
`B0140.IsTrain` that do not involve the decaying gauge, the stream function or oddness. -/
structure IsClassicalOn (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) : Prop where
  smooth_v : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ univ)
  smooth_p : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p x.1 x.2) (Icc 0 T ×ˢ univ)
  periodic_v : ∀ s ∈ Icc 0 T, Cyl.IsPeriodic c (v s)
  periodic_p : ∀ s ∈ Icc 0 T, Cyl.IsPeriodic c (p s)
  solenoidal : ∀ s ∈ Icc 0 T, ∀ z, Cyl.divergence (v s) z = 0
  momentum : ∀ s ∈ Ioo 0 T, ∀ z, Train.momentumResidual ν v p s z = 0
  initial : v 0 = trainDatum c
  finite_energy : ∀ s ∈ Icc 0 T, IntegrableOn (fun z => ‖v s z‖ ^ 2) (Cyl.cell c)

/-- `B0140.IsTrain` restricted to the time interval `[0,T]` (tex lines 2045-2051, 2141-2161). -/
structure IsTrainOn (ν c T : ℝ) (v : ℝ → Plane → Vec) (p ψ : ℝ → Plane → ℝ) : Prop where
  smooth_v : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ univ)
  smooth_p : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p x.1 x.2) (Icc 0 T ×ˢ univ)
  periodic_v : ∀ s ∈ Icc 0 T, Cyl.IsPeriodic c (v s)
  periodic_p : ∀ s ∈ Icc 0 T, Cyl.IsPeriodic c (p s)
  solenoidal : ∀ s ∈ Icc 0 T, ∀ z, Cyl.divergence (v s) z = 0
  momentum : ∀ s ∈ Ioo 0 T, ∀ z, Train.momentumResidual ν v p s z = 0
  initial : v 0 = trainDatum c
  finite_energy : ∀ s ∈ Icc 0 T, IntegrableOn (fun z => ‖v s z‖ ^ 2) (Cyl.cell c)
  pressure_decay : ∀ s ∈ Icc 0 T, Tendsto (p s) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)
  stream_differentiable : ∀ s ∈ Icc 0 T, Differentiable ℝ (ψ s)
  stream : ∀ s ∈ Icc 0 T, ∀ z, v s z = toVec (perpendicularGradient (ψ s) z)
  stream_decay : ∀ s ∈ Icc 0 T, Tendsto (ψ s) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)
  odd : ∀ s ∈ Icc 0 T, ∀ z, v s (-z) = -v s z

/-- A global train restricts to a train on `[0,T]` (sanity check of `IsTrainOn`). -/
theorem isTrainOn_of_isTrain {ν c : ℝ} {v : ℝ → Plane → Vec} {p ψ : ℝ → Plane → ℝ}
    (h : B0140.IsTrain ν c v p ψ) (T : ℝ) : IsTrainOn ν c T v p ψ where
  smooth_v := h.smooth_v.mono (prod_mono Icc_subset_Ici_self subset_rfl)
  smooth_p := h.smooth_p.mono (prod_mono Icc_subset_Ici_self subset_rfl)
  periodic_v s hs := h.periodic_v s hs.1
  periodic_p s hs := h.periodic_p s hs.1
  solenoidal s hs := h.solenoidal s hs.1
  momentum s hs := h.momentum s hs.1
  initial := h.initial
  finite_energy s hs := h.finite_energy s hs.1
  pressure_decay s hs := h.pressure_decay s hs.1
  stream_differentiable s hs := h.stream_differentiable s hs.1
  stream s hs := h.stream s hs.1
  stream_decay s hs := h.stream_decay s hs.1
  odd s hs := h.odd s hs.1

/-- All spatial derivatives of `v` are bounded, uniformly on `[0,T]`. -/
def HasBoundedDerivsOn (T : ℝ) (v : ℝ → Plane → Vec) : Prop :=
  ∀ k : ℕ, ∃ M : ℝ, ∀ s ∈ Icc 0 T, ∀ z, ‖iteratedFDeriv ℝ k (v s) z‖ ≤ M

/-- The velocity tends to `0` as `|η| → ∞`, for every `s ∈ [0,T]`. -/
def VelocityDecayOn (T : ℝ) (v : ℝ → Plane → Vec) : Prop :=
  ∀ s ∈ Icc 0 T, Tendsto (v s) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)

/-- The pressure tends to `0` as `|η| → ∞` (the decaying gauge), for every `s ∈ [0,T]`. -/
def PressureDecayOn (T : ℝ) (p : ℝ → Plane → ℝ) : Prop :=
  ∀ s ∈ Icc 0 T, Tendsto (p s) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)

/-- The velocity is centrally odd, for every `s ∈ [0,T]`. -/
def IsOddOn (T : ℝ) (v : ℝ → Plane → Vec) : Prop :=
  ∀ s ∈ Icc 0 T, ∀ z, v s (-z) = -v s z

/-- The first moment of the vorticity in `η` is finite on the cell, for every `s ∈ [0,T]`. -/
def VorticityMomentOn (c T : ℝ) (v : ℝ → Plane → Vec) : Prop :=
  ∀ s ∈ Icc 0 T, IntegrableOn (fun z : Plane => (1 + |z.2|) * |Cyl.curl (v s) z|) (Cyl.cell c)

/-- `ψ` is a decaying stream for `v` on `[0,T]`: `v = ∇^⊥ψ`, `ψ` differentiable, `ψ → 0` as
`|η| → ∞`. -/
def StreamOn (T : ℝ) (v : ℝ → Plane → Vec) (ψ : ℝ → Plane → ℝ) : Prop :=
  ∀ s ∈ Icc 0 T, Differentiable ℝ (ψ s) ∧ (∀ z, v s z = toVec (perpendicularGradient (ψ s) z)) ∧
    Tendsto (ψ s) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)

/-- **The target of `PartI:T02`** (tex lines 261-285, Gallay-Slijepcevic Theorem 1.1, local part):
for `ν > 0` and `c ≥ 1` there is `T > 0` and a classical train on `[0,T]`. -/
def TrainLocalClassical : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c →
    ∃ T : ℝ, 0 < T ∧ ∃ (v : ℝ → Plane → Vec) (p ψ : ℝ → Plane → ℝ), IsTrainOn ν c T v p ψ

/-- **Step 1** (mild `H³` solution to classical solution; lines 261-285): there is `T > 0` and a
classical solution on `[0,T]` with the datum `trainDatum c`, with all spatial derivatives bounded
and the velocity decaying in `|η|`. -/
def LocalClassicalBounded : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c →
    ∃ T : ℝ, 0 < T ∧ ∃ (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ),
      IsClassicalOn ν c T v p ∧ HasBoundedDerivsOn T v ∧ VelocityDecayOn T v

/-- **Step 2** (decaying pressure gauge, line 447): a classical solution with bounded derivatives
and decaying velocity has a classical pressure (changed by a function of `s`) that tends to `0` as
`|η| → ∞`. -/
def LerayPressureGauge : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c → 0 < T →
    IsClassicalOn ν c T v p → HasBoundedDerivsOn T v → VelocityDecayOn T v →
    ∃ p' : ℝ → Plane → ℝ, IsClassicalOn ν c T v p' ∧ PressureDecayOn T p'

/-- **Step 3** (line 288, "Uniqueness gives `v(-q,-η,s) = -v(q,η,s)`"): a classical solution with
bounded derivatives and decaying pressure is centrally odd (uniqueness for the reflected pair
`(-v(s,-z), p(s,-z))`, which has the same odd datum). -/
def ClassicalOdd : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c → 0 < T →
    IsClassicalOn ν c T v p → HasBoundedDerivsOn T v → PressureDecayOn T p → IsOddOn T v

/-- **Step 4** (vorticity equation with weight `1 + |η|`; lines 276-288): the first moment of the
vorticity of a classical solution with bounded derivatives is finite. -/
def VorticityFirstMoment : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c → 0 < T →
    IsClassicalOn ν c T v p → HasBoundedDerivsOn T v → VorticityMomentOn c T v

/-- **Step 5** (decaying stream, tex line 2049): an odd classical solution with bounded derivatives
and finite vorticity first moment has a decaying stream. -/
def StreamExists : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c → 0 < T →
    IsClassicalOn ν c T v p → HasBoundedDerivsOn T v → IsOddOn T v → VorticityMomentOn c T v →
    ∃ ψ : ℝ → Plane → ℝ, StreamOn T v ψ

/-- **The local classical train from the five steps.**  The unconditional statement is
`PartI:T02`. -/
theorem train_local_classical_of (h1 : LocalClassicalBounded) (h2 : LerayPressureGauge)
    (h3 : ClassicalOdd) (h4 : VorticityFirstMoment) (h5 : StreamExists) : TrainLocalClassical := by
  intro ν c hν hc
  obtain ⟨T, hT, v, p, hcl, hb, hdec⟩ := h1 ν c hν hc
  obtain ⟨p', hcl', hp'⟩ := h2 ν c T v p hν hc hT hcl hb hdec
  have hodd : IsOddOn T v := h3 ν c T v p' hν hc hT hcl' hb hp'
  have hmom : VorticityMomentOn c T v := h4 ν c T v p' hν hc hT hcl' hb
  obtain ⟨ψ, hψ⟩ := h5 ν c T v p' hν hc hT hcl' hb hodd hmom
  exact ⟨T, hT, v, p', ψ,
    { smooth_v := hcl'.smooth_v
      smooth_p := hcl'.smooth_p
      periodic_v := hcl'.periodic_v
      periodic_p := hcl'.periodic_p
      solenoidal := hcl'.solenoidal
      momentum := hcl'.momentum
      initial := hcl'.initial
      finite_energy := hcl'.finite_energy
      pressure_decay := hp'
      stream_differentiable := fun s hs => (hψ s hs).1
      stream := fun s hs => (hψ s hs).2.1
      stream_decay := fun s hs => (hψ s hs).2.2
      odd := hodd }⟩

end UnforcedLeray.Short.PartI
