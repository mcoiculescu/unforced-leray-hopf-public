import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Part I, task `PartI:T05`: uniqueness of the train (audit file)

Source of record: `the November 2 reference manuscript`, lines 276-288 ("It gives a
unique global mild solution in BUC ... It is also the finite-energy solution ...").

## Audit finding: the former `TrainUniqueness` is false as stated

The former statement, kept here as `TrainUniquenessAllAges`, asserts `tr.v = tr'.v` as
functions on all of `ℝ`, including negative ages `s < 0`.  Every field of `B0140.IsTrain` constrains
`v` only at `s ≥ 0` (or on `Ici 0 ×ˢ univ`), so a train solution can be altered at negative ages
without leaving the class.  `not_trainUniqueness_of_solvable` proves this: whenever
`TrainIVPSolvable ν c` holds, the statement `TrainUniquenessAllAges` is refutable.

**Update (organizer `ORG:train-class`).**  `StatementsTrain.lean` now states `TrainUniqueness` as
forward uniqueness (`s ≥ 0`) *within the BUC class* `IsBUCTrain` (`TrainClass.lean`), and
`TrainGlobalExistence` as non-emptiness of that class.  It is proved from the classical-solution
uniqueness machinery of `Sub/T02_3.lean` in `Sub/T05Class.lean`.  The leaves below
(`TrainLocalBounds`, `TrainCutoffEnergyIneq`, `TrainDiffEnergyZero`, `TrainEnergyZeroToEq`,
`TrainUniquenessFwd`) are the earlier route for *arbitrary* `TrainSol`; `TrainLocalBounds`, hence
`TrainDiffEnergyZero` and `TrainUniquenessFwd`, are not derivable from `IsTrain` and are kept only
because accepted files (`TrainCutoffEnergyProof`, `TrainDiffEnergyZeroProof`,
`TrainEnergyZeroToEqProof`) are stated against them; the live statement is `TrainUniqueness`.

## Corrected statement and decomposition

The corrected statement is `TrainUniquenessFwd` (equality of `v s` for `s ≥ 0`).  It is proved from
the leaves below, whose statements are exact.  The remaining analytic input is `TrainLocalBounds`
(time-local boundedness), which is the Gallay-Slijepcevic BUC bound (source lines 276-282) and is
**not** derivable from the fields of `B0140.IsTrain` (finite energy is only pointwise in `s`).

* `TrainLocalBounds` : sup bounds on `v`, `p` and cell `L²` bounds on every `[0, S]`.
* `TrainCutoffEnergyIneq` : the transverse-cutoff energy inequality of the difference of two trains,
  `F_R(s) ≤ C ∫₀ˢ F_R + C/√R`, with `C` independent of the cutoff radius `R`.
* `TrainDiffEnergyZero` : the cell energy of the difference vanishes at every age `s ≥ 0`.
* `TrainEnergyZeroToEq` : vanishing cell energy of a continuous periodic difference forces equality.

Conditional theorem `trainUniquenessFwd_of` is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### The former `TrainUniqueness` is refutable -/

/-- The former statement of uniqueness (equality of `v` on all of `ℝ`, including negative ages),
which is false whenever a train exists. -/
def TrainUniquenessAllAges : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, tr.v = tr'.v

/-- Alter a train velocity at negative ages by a constant vector `e`. -/
def shiftV {ν c : ℝ} (tr : B0140.TrainSol ν c) (e : Vec) : ℝ → Plane → Vec :=
  fun s z => if s < 0 then tr.v s z + e else tr.v s z

theorem shiftV_of_nonneg {ν c : ℝ} (tr : B0140.TrainSol ν c) (e : Vec) {s : ℝ} (hs : 0 ≤ s) :
    shiftV tr e s = tr.v s := by
  funext z
  simp [shiftV, not_lt.2 hs]

theorem shiftV_eventuallyEq {ν c : ℝ} (tr : B0140.TrainSol ν c) (e : Vec) {s : ℝ} (hs : 0 < s)
    (z : Plane) : (fun t => shiftV tr e t z) =ᶠ[𝓝 s] fun t => tr.v t z := by
  filter_upwards [Ioi_mem_nhds hs] with t ht
  simp [shiftV, not_lt.2 (le_of_lt (Set.mem_Ioi.1 ht))]

/-- A second train solution with the same data at all ages `s ≥ 0` and a different `v` at `s < 0`. -/
def trainShiftNeg {ν c : ℝ} (tr : B0140.TrainSol ν c) (e : Vec) : B0140.TrainSol ν c where
  v := shiftV tr e
  p := tr.p
  ψ := tr.ψ
  isTrain :=
    { smooth_v := tr.isTrain.smooth_v.congr (fun x hx => by
        show shiftV tr e x.1 x.2 = tr.v x.1 x.2
        rw [shiftV_of_nonneg tr e (Set.mem_Ici.1 hx.1)])
      smooth_p := tr.isTrain.smooth_p
      periodic_v := fun s hs => by
        rw [shiftV_of_nonneg tr e hs]
        exact tr.isTrain.periodic_v s hs
      periodic_p := tr.isTrain.periodic_p
      solenoidal := fun s hs z => by
        rw [shiftV_of_nonneg tr e hs]
        exact tr.isTrain.solenoidal s hs z
      momentum := fun s hs z => by
        have h := tr.isTrain.momentum s hs z
        unfold Train.momentumResidual at h ⊢
        rw [(shiftV_eventuallyEq tr e hs z).deriv_eq, shiftV_of_nonneg tr e hs.le]
        exact h
      initial := by
        rw [shiftV_of_nonneg tr e le_rfl]
        exact tr.isTrain.initial
      finite_energy := fun s hs => by
        rw [shiftV_of_nonneg tr e hs]
        exact tr.isTrain.finite_energy s hs
      pressure_decay := tr.isTrain.pressure_decay
      stream_differentiable := tr.isTrain.stream_differentiable
      stream := fun s hs z => by
        rw [shiftV_of_nonneg tr e hs]
        exact tr.isTrain.stream s hs z
      stream_decay := tr.isTrain.stream_decay
      odd := fun s hs z => by
        rw [shiftV_of_nonneg tr e hs]
        exact tr.isTrain.odd s hs z }

/-- **The former `TrainUniqueness` is false whenever a train exists.**  The velocity
of a `TrainSol` at negative ages is unconstrained, so two train solutions need not have equal `v`. -/
theorem not_trainUniqueness_of_solvable {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (h : B0140.TrainIVPSolvable ν c) : ¬ TrainUniquenessAllAges := by
  intro hU
  obtain ⟨tr⟩ := h
  have heq := hU ν c hν hc tr (trainShiftNeg tr (EuclideanSpace.single 0 1))
  have h1 := congrFun (congrFun heq (-1)) 0
  have h2 : (trainShiftNeg tr (EuclideanSpace.single 0 1)).v (-1) 0 =
      tr.v (-1) 0 + EuclideanSpace.single 0 1 := by
    simp [trainShiftNeg, shiftV]
  rw [h2] at h1
  have h3 : (EuclideanSpace.single 0 1 : Vec) = 0 := by
    have h4 : tr.v (-1) 0 + (EuclideanSpace.single 0 1 : Vec) = tr.v (-1) 0 + 0 := by
      rw [add_zero]
      exact h1.symm
    exact add_left_cancel h4
  have h5 := congrArg (fun x : Vec => x 0) h3
  simp at h5

/-- **`TrainGlobalExistence` and the former `TrainUniqueness` are jointly inconsistent.** -/
theorem trainGlobalExistence_not_trainUniqueness (hex : TrainGlobalExistence) :
    ¬ TrainUniquenessAllAges := by
  obtain ⟨tr, -⟩ := hex 1 1 one_pos le_rfl
  exact not_trainUniqueness_of_solvable (ν := 1) (c := 1) one_pos one_pos ⟨tr⟩

/-! ### The corrected statement -/

/-- **Uniqueness of the train (corrected)**: two train solutions have the same velocity at every
age `s ≥ 0` (lines 276-288).  Equality of `v` on negative ages is not a property of the class. -/
def TrainUniquenessFwd : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ s : ℝ, 0 ≤ s → tr.v s = tr'.v s

/-! ### The leaves -/

/-- Bounds of a train on `[0, S]` by `M`: sup of the velocity and of the pressure, and the
unnormalized cell energy. -/
def TrainBoundedBy {ν c : ℝ} (tr : B0140.TrainSol ν c) (S M : ℝ) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) S, (∀ z : Plane, ‖tr.v s z‖ ≤ M) ∧ (∀ z : Plane, |tr.p s z| ≤ M) ∧
    ∫ z in Cyl.cell c, ‖tr.v s z‖ ^ 2 ≤ M

/-- **Time-local bounds of the train** (source lines 276-282: the solution is in `BUC`, and the mild
equation in `BUC ∩ L²` gives `‖v(t)‖₂ ≤ ‖v(0)‖₂ + C ν^{-1/2} sup‖v‖_∞ ∫ (t-r)^{-1/2} ‖v(r)‖₂ dr`;
bounded periodic pressure): on every `[0, S]` the velocity and pressure are bounded and the cell
energy is bounded.  This is the Gallay-Slijepcevic input; it is **not** a consequence of the
fields of `B0140.IsTrain` (whose finite energy is only pointwise in `s`).  If the drafters confirm
this, `B0140.IsTrain` must be strengthened by the author with such a field, or the statement
restricted to the BUC class. -/
def TrainLocalBounds : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ S : ℝ, 0 ≤ S → ∃ M : ℝ,
    TrainBoundedBy tr S M

/-- The smooth transverse cutoff squared: `ζ(2 - |η|/R)²`, equal to `1` for `|η| ≤ R` and to `0` for
`|η| ≥ 2R`, with `ζ = Real.smoothTransition`.  (A square, so that `|φ'| ≤ C ζ / R`.) -/
def etaCutoff (R η : ℝ) : ℝ := Real.smoothTransition (2 - |η| / R) ^ 2

/-- The cutoff energy `F_R(s) = ∫_{cell} φ_R(η) |v(s) - v'(s)|²` of the difference of two trains. -/
def cutoffEnergy {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * ‖tr.v s z - tr'.v s z‖ ^ 2

/-- **Cutoff energy inequality** (energy method, source lines 276-288 and the classical uniqueness
argument for the cylinder Navier-Stokes system).  If two trains are bounded by `M` on `[0, S]`
(`TrainBoundedBy`), there is `C` independent of `R` such that for every `R ≥ 1` the cutoff energy of
the difference is continuous on `[0, S]` and satisfies
`F_R(s) ≤ C ∫₀ˢ F_R(r) dr + C / √R`.
(Derivation: `w = v - v'` solves `w_s + v·∇w + w·∇v' - νΔw + ∇(p-p') = 0`, `F_R(0) = 0`;
test with `φ_R w`; the viscous term gives `-2ν∫φ|∇w|²` plus a cross term absorbed using
`φ = ζ²`; `∫φ w·(w·∇v') = -∫φ (w·∇w)·v' - ∫ (w·∇φ)(w·v')` uses `div w = 0` and bounds only `‖v'‖_∞`;
the transport term is `≤ M ‖∇φ‖_∞ ∫_{R≤|η|≤2R} |w|² = O(1/R)`; the pressure term is
`≤ 2·2M ‖∇φ‖_∞ ∫_{R≤|η|≤2R} |w| = O(R^{-1/2})` by Cauchy-Schwarz on a strip of measure `≤ 2Rc`.) -/
def TrainCutoffEnergyIneq : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ S M : ℝ, 0 ≤ S →
    TrainBoundedBy tr S M → TrainBoundedBy tr' S M →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ContinuousOn (cutoffEnergy tr tr' R) (Icc 0 S) ∧
      ∀ s ∈ Icc (0 : ℝ) S,
        cutoffEnergy tr tr' R s ≤
          C * (∫ r in (0 : ℝ)..s, cutoffEnergy tr tr' R r) + C / Real.sqrt R

/-- The cell energy of the difference of two trains vanishes at every age `s ≥ 0`. -/
def TrainDiffEnergyZero : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ s : ℝ, 0 ≤ s →
    ∫ z in Cyl.cell c, ‖tr.v s z - tr'.v s z‖ ^ 2 = 0

/-- A continuous `c`-periodic difference with vanishing cell energy vanishes (measure theory: the
set `{w ≠ 0}` is open, `c`-periodic, and null on the cell, hence null on the plane, hence empty). -/
def TrainEnergyZeroToEq : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ s : ℝ, 0 ≤ s →
    ∫ z in Cyl.cell c, ‖tr.v s z - tr'.v s z‖ ^ 2 = 0 → tr.v s = tr'.v s

/-! ### The conditional theorem -/

/-- **`PartI:T05`, corrected target, conditional form.** -/
theorem trainUniquenessFwd_of (hZ : TrainDiffEnergyZero) (hP : TrainEnergyZeroToEq) :
    TrainUniquenessFwd :=
  fun ν c hν hc tr tr' s hs => hP ν c hν hc tr tr' s hs (hZ ν c hν hc tr tr' s hs)

end UnforcedLeray.Short.PartI
