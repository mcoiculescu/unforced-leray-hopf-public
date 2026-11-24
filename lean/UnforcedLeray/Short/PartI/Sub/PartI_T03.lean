import UnforcedLeray.Short.PartI.TrainClass
import UnforcedLeray.Units.B0140

/-!
# Part I, task `PartI:T03` (audit decomposition): vorticity bounds of the train

Source of record: `the November 2 reference manuscript`, lines 276-288: "The scalar
vorticity equation preserves zero circulation and its `L¹, L^∞` bounds."

`ω(s) = Cyl.curl (tr.v s)` for the train `tr : B0140.TrainSol ν c` of the class `IsBUCTrain`, and
`ω₀ = ω(0) = Cyl.curl (tr.v 0)` (`tr.isTrain.initial : v 0 = trainDatum c`; datum bounds
`Train.abs_curl_datum_le`, `Train.integral_cell_curl_datum` in `Lib/Train/Datum.lean`).
The three claims are the three lemma `Prop`s below; `trainVorticityBounds_of` combines them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- `L^∞` bound (source 276-288): `‖ω(s)‖_∞ ≤ ‖ω₀‖_∞`, stated as: any bound `M` for `|ω₀|`
bounds `|ω(s)|` for every `s ≥ 0`.  Proof: maximum principle for
`ω_s + v·∇ω = νΔω` on the cylinder with bounded drift, exhaustion/barrier
(`Tasks/VorticityFirstMoment/ParabolicMinPrinciple.lean`, `localVorticityEquation`). -/
def TrainVorticityLinf : Prop :=
  ∀ (ν c : ℝ), 0 < ν → 2 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ M : ℝ, (∀ z : Plane, |Cyl.curl (tr.v 0) z| ≤ M) →
      ∀ s : ℝ, 0 ≤ s → ∀ z : Plane, |Cyl.curl (tr.v s) z| ≤ M

/-- `L¹` bound on one cell (source 276-288): `‖ω(s)‖_{L¹(cell)} ≤ ‖ω₀‖_{L¹(cell)}` as an inequality
of `ℝ≥0∞`-valued integrals (no junk values).  Proof: Kato / sign truncation
`sqrt(ω²+ε²)` for `ω_s + v·∇ω = νΔω`, periodic in `q`, with `η`-cutoff
(decay of `ω` from `VorticityFirstMoment`, `Short/PartI/Sub/T02.lean`). -/
def TrainVorticityL1 : Prop :=
  ∀ (ν c : ℝ), 0 < ν → 2 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ s : ℝ, 0 ≤ s →
      ∫⁻ z in Cyl.cell c, ‖Cyl.curl (tr.v s) z‖ₑ ≤ ∫⁻ z in Cyl.cell c, ‖Cyl.curl (tr.v 0) z‖ₑ

/-- Zero circulation (source 276-288): `ω(s)` is integrable over one cell and `∫_cell ω(s) = 0`.
Proof: `d/ds ∫_cell ω = ∫_cell (νΔω - v·∇ω) = 0` (periodicity in `q`, decay in `η`),
datum `Train.integral_cell_curl_datum`. -/
def TrainVorticityCirculation : Prop :=
  ∀ (ν c : ℝ), 0 < ν → 2 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ s : ℝ, 0 ≤ s →
      IntegrableOn (fun z => Cyl.curl (tr.v s) z) (Cyl.cell c) ∧
        ∫ z in Cyl.cell c, Cyl.curl (tr.v s) z = 0

/-- The three vorticity facts together. -/
def TrainVorticityBoundsStmt : Prop :=
  TrainVorticityLinf ∧ TrainVorticityL1 ∧ TrainVorticityCirculation

theorem trainVorticityBounds_of (h1 : TrainVorticityLinf) (h2 : TrainVorticityL1)
    (h3 : TrainVorticityCirculation) : TrainVorticityBoundsStmt := ⟨h1, h2, h3⟩

end UnforcedLeray.Short.PartI
