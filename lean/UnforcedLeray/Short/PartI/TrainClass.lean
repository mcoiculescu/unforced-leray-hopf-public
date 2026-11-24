import UnforcedLeray.Short.PartI.Sub.T02

/-!
# Part I: the Gallay-Slijepcevic (BUC) class of trains

Source of record: `the November 2 reference manuscript`, lines 270-288: "It gives a
unique global mild solution in `BUC`, smooth for positive time, with the bounded periodic pressure
choice.  It is also the finite-energy solution ... Uniqueness gives `v(-q,-η,s) = -v(q,η,s)`."

## Why a class

`B0140.IsTrain` constrains the train only pointwise in the age `s`: its fields give joint
smoothness of `v` on `[0,∞) × ℝ²` and, for each fixed `s`, finite energy, decaying pressure,
decaying stream and oddness.  Nothing in it is uniform in `s`, so (audit findings of the Part I
auditors, ledger ids `PartI:T05`, `PartI:T01/1`, `PartI:T01/2`, `PartI:T05b/1`):

* uniqueness of the train is *not derivable* from `IsTrain` (no time-local bounds), and the former
  statement `tr.v = tr'.v` on all of `ℝ` was false (`IsTrain` ignores `s < 0`);
* the smoothness and the age decay of the stream `ψ` are not derivable from `IsTrain`.

The train of the source is the Gallay-Slijepcevic solution in `BUC`: bounded, uniformly continuous,
with all spatial derivatives bounded on every finite time interval `[0, S]`.  `IsBUCTrain tr`
records exactly this additional regularity of the library's train `tr : B0140.TrainSol ν c`
(`B0140` itself is not modified: the class wraps it).  It uses the same predicate as the local
classical train of `Sub/T02.lean`, `HasBoundedDerivsOn S v`: `∀ k, ∃ M, ∀ s ∈ [0,S], ∀ z,
‖D^k v(s,z)‖ ≤ M`.

All Part I statements about the train (`StatementsTrain.lean`) are stated for trains in this
class; `TrainGlobalExistence` asserts that the class is non-empty for every period `c ≥ 1`
(the periods of the paper are `c = ν^{-ρ} ≥ 1`), and `TrainUniqueness` that two members of
the class agree for `s ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **The BUC class of trains** (source lines 270-288): a train `tr : B0140.TrainSol ν c` whose
velocity has, for every `S ≥ 0`, all spatial derivatives (orders `k = 0, 1, 2, …`) bounded on
`[0, S] × ℝ²`.  `HasBoundedDerivsOn S v` is the predicate of `Sub/T02.lean`. -/
def IsBUCTrain {ν c : ℝ} (tr : B0140.TrainSol ν c) : Prop :=
  ∀ S : ℝ, 0 ≤ S → HasBoundedDerivsOn S tr.v

/-- The class is non-empty at the pair `(ν, c)`: the global existence statement for the BUC
class (Gallay-Slijepcevic, Theorem 1.1 and Remark 1.3(2)). -/
def TrainBUCSolvable (ν c : ℝ) : Prop :=
  ∃ tr : B0140.TrainSol ν c, IsBUCTrain tr

namespace IsBUCTrain

/-- Unfolded form: every spatial derivative order is bounded on `[0, S] × ℝ²`. -/
theorem deriv_bound {ν c : ℝ} {tr : B0140.TrainSol ν c} (h : IsBUCTrain tr) {S : ℝ}
    (hS : 0 ≤ S) (k : ℕ) :
    ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) S, ∀ z : Plane, ‖iteratedFDeriv ℝ k (tr.v s) z‖ ≤ M :=
  h S hS k

/-- The velocity itself (order `k = 0`) is bounded on `[0, S] × ℝ²`. -/
theorem sup_bound {ν c : ℝ} {tr : B0140.TrainSol ν c} (h : IsBUCTrain tr) {S : ℝ}
    (hS : 0 ≤ S) : ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) S, ∀ z : Plane, ‖tr.v s z‖ ≤ M := by
  obtain ⟨M, hM⟩ := h S hS 0
  exact ⟨M, fun s hs z => by simpa [norm_iteratedFDeriv_zero] using hM s hs z⟩

end IsBUCTrain

/-- A train, restricted to `[0, T]`, is a classical solution in the sense of `Sub/T02.lean`. -/
theorem trainSol_isClassicalOn {ν c : ℝ} (tr : B0140.TrainSol ν c) (T : ℝ) :
    IsClassicalOn ν c T tr.v tr.p :=
  let h := isTrainOn_of_isTrain tr.isTrain T
  { smooth_v := h.smooth_v
    smooth_p := h.smooth_p
    periodic_v := h.periodic_v
    periodic_p := h.periodic_p
    solenoidal := h.solenoidal
    momentum := h.momentum
    initial := h.initial
    finite_energy := h.finite_energy }

/-- The pressure of a train decays in `|η|` at every age `s ∈ [0, T]`. -/
theorem trainSol_pressureDecayOn {ν c : ℝ} (tr : B0140.TrainSol ν c) (T : ℝ) :
    PressureDecayOn T tr.p :=
  fun s hs => tr.isTrain.pressure_decay s hs.1

end UnforcedLeray.Short.PartI
