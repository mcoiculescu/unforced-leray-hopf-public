import UnforcedLeray.Blueprint.Construction.Compose
import UnforcedLeray.Cons.C02PhaseLocked
import UnforcedLeray.Cons.C09PressureProjection
import UnforcedLeray.Loc.AssemblyB

/-!
# The concrete construction data, and `ConstructionClaim` from existence statements

`paper/main.tex`, completion of the construction (lines 13714–13745, blueprint B1033) and
the choices it fixes (lines 13608–13651, 13714–13725). `ConstructionClaim`
(`prop:unstable-background`, lines 150–191, B1034) is reduced in
`Blueprint/Construction/Compose.lean` to the steps C1–C9 on one `ConstructionData`. This file
builds that record and reduces `ConstructionClaim` to named existence statements, one per
open step, each a statement the manuscript proves.

## The record

`Reference.data R S` is the `ConstructionData` of the final theorem:
* `planar`, `σ₀`: the reference `R` (`λ, q, q†, V_can` and `σ₀ = μ₀`), from the existence
  statement C1 (`ReferenceChoiceExists`, by `Classical.choose` in

  (`Lib/ComplexODEC` has no `GaussianGrowingMode`), so C1 stays a named existence statement.
* `ν`: the phase-locked sequence of C2 (`ConstructionData.phaseLockedNu`,
  `Cons/C02PhaseLocked.lean`), built from `planar` and `σ₀` only.
* explicit, from `planar`, `σ₀`, `ν` only (`Steps.lean`): `ε_n`, `c_n`, `P_n = 2ε_nc_n`,
  `R_n = ε_n⁻¹`, `ℓ_n`, the window, `K₀`, the inlet streams. They do not depend on `S`
  (`data_period`, `data_window`, ... are `rfl`).
* `a, U, Q, p, observation`: at level `n`, `Classical.choose` of Theorem B3 at
  `(ν_n, P_n)` (`TheoremB3`), within the class `S n` (`levelChoice`).
* `Bfull n σ`: `Classical.choose` of the reduced matrix at `σ` on the chosen background and
  observation (`ReducedMatrixExists`, `reducedMatrix`).

## Why a class `S` of level choices

`IsB3Output` does not determine the background, and the admissibility clauses do not
determine the observation (`Steps.lean`, module docstring). C6 and C7 are proved in the
manuscript for the objects that Lemma `lem:late-stress-3-10` (the "common choice",
lines 10688–10868, B0725) fixes: "Apply Lemma 3-10 ..., fixing its background, loss targets
and compact observation" (lines 13380–13383), with the background of Theorem B3 (lines
13718–13722). They are false for an arbitrary background meeting `IsB3Output` with an
arbitrary admissible observation. So the existence statements are relative to a predicate
`S n r` on level choices `r = (a, U, Q, p, C_H)`, standing for "`r` is the common choice of
Lemma 3-10 at level `n`, with the background of Theorem B3". The manuscript proves the
existence statements for that predicate. The reduction holds for every `S`; any `S` for which
the statements hold gives `ConstructionClaim`. A one-point class `S n r ↔ r = train n` is the
special case of an explicit selection.

## The existence statements

| Step | Prop | Manuscript statement | Units |
|---|---|---|---|
| C1 | `ReferenceChoiceExists`, `Reference.IsReferenceChoice` | G1–G4 (lines 691–800), `-2 < ω < 0` (t00008, line 696), `μ₀ ∈ (1/16,1/8)` with `𝒞(μ₀) ≠ 0` (t00755, lines 13196–13213) | B0085, B0882 |
| C3 | `Reference.TheoremB3` | Theorem B3 (lines 5093–5141) at `(ν_n, P_n)` with the common choice (lines 13608–13616, 13714–13725) | B0705, B0725 |
| C6 | `Reference.UniformReducedReturn` | `prop:uniform-reduced-return` (lines 13377–13422), with `G = G_H` (lines 13653–13660) | B0992, B1000 |
| C7 | `Reference.ReducedMatrixExists` | Section `sec:st18-12887` (lines 10870–10900), `eq:m4-inverse-blocks` (lines 9738–9750), `prepared:p4.3` (lines 9554–9563), line 13655 | B0747, B0770, B0771, B0596, B1004 |
| C8 | `StepPhysicalMode` (`Steps.lean`) | t00633 (lines 10900–10911), lines 13693–13707 | B0773, B1005, B1006 |

Discharged by proved theorems: C2 (`ConstructionData.stepPhaseLocked_of_C1`), C4 and C5
(inside `constructionClaim_of_steps`, from `stepGainTrace_of`, `stepGainBound_of`), C9
(`pressureProjectionStep`, `Cons/C09PressureProjection.lean`).

Main results:
* `Reference.constructionSteps`: C1, C2, C3, C6, C7 for `R.data S`.
* `constructionClaim_of_reference`: `ConstructionClaim` from C1, C3, C6, C7 for one explicit
  reference `R` and class `S`, and C8.
* `constructionClaim_of_existence`: the same with the reference chosen from
  `ReferenceChoiceExists` by `Classical.choose` (C3, C6, C7 then for every reference
  meeting C1).
* `constructionClaim_of_constructionExistence`: from the single weakest statement
  `ConstructionExistence` (some reference and some class with C1, C3, C6, C7) and C8.
* `mainClaim_of_existence`: Theorem A from the same, by the compiled localization half
  (`Loc/AssemblyB.lean`, `mainClaim_of_constructionClaim`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Matrix
open scoped Topology

namespace UnforcedLeray.Cons.Data

open UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar MatrixCrossing

/-! ## The reference and the level choices -/

/-- The reference choice of lines 13608–13617: the planar data `(λ, q, q†, V_can)` of G1–G4
(lines 691–800, B0085) and `σ₀ = μ₀` (t00755, line 13208, B0882). -/
structure Reference where
  /-- `(λ, q, q†, V_can)`. -/
  planar : PlanarData
  /-- `σ₀ = μ₀ ∈ (1/16, 1/8)`. -/
  σ₀ : ℝ

/-- The objects fixed at one level `n` (lines 13714–13725): the DSS datum `a` (2.8), the
exact background `U` (2.4), `Q = U - H_ν[a]` (2.10), the global pressure `p` (Theorem B3,
lines 5093–5141, B0705) and the fixed averaged observation `C_H` (`prepared:p4.3`,
lines 9554–9563, B0596). -/
structure LevelChoice where
  /-- The DSS datum `a`. -/
  a : SpatialField
  /-- The exact background `U`. -/
  U : ℝ → SpatialField
  /-- The heat remainder `Q`. -/
  Q : ℝ → SobolevGraph.H2
  /-- The global pressure `p`. -/
  p : ℝ → Space → ℝ
  /-- The observation `C_H`. -/
  observation : ObservationData

/-- A placeholder level choice, used only at levels where no statement is asserted. -/
def LevelChoice.zero : LevelChoice :=
  ⟨fun _ => 0, fun _ _ => 0, fun _ => 0, fun _ _ => 0, ⟨0, 0, fun _ => 0, fun _ _ => 0⟩⟩

namespace Reference

variable (R : Reference)

/-- The record with the reference data and every other field zero. Only its `planar` and
`σ₀` are used: the phase-locked sequence and every explicit quantity depend on nothing else. -/
def seed : ConstructionData where
  planar := R.planar
  σ₀ := R.σ₀
  ν := fun _ => 0
  a := fun _ => 0
  U := fun _ _ => 0
  Q := fun _ _ => 0
  p := fun _ _ _ => 0
  observation := fun _ => LevelChoice.zero.observation
  Bfull := fun _ _ => 0

/-- The reference with the phase-locked viscosities `ν_n` of `eq:st18-t00763`
(lines 13618–13626, B0997). Its explicit quantities (`ε_n`, `P_n`, `R_n`, `c_n`, the window,
`K₀`, the inlet streams) are those of the final record `data`. -/
def base : ConstructionData := R.seed.withPhaseLocked

/-- **C1** for a reference: G1–G4 for the planar data (lines 691–800, B0085), `-2 < ω < 0`
(`eq:st18-t00008`, line 696), `σ₀ ∈ (1/16, 1/8)` with `𝒞(σ₀) ≠ 0` (`eq:st18-t00755`,
lines 13196–13213, B0882; the manuscript chooses `μ₀` with `J(μ₀) ≠ 0`, and the other
factors of `𝒞` are nonzero, lines 13196–13204), and `𝓙` continuous at `σ₀` (G4: `J` is
holomorphic on `Re μ > -3/2`, line 13197). This is `StepReferenceChoice` for any record with
this reference (`stepReferenceChoice_data`). -/
def IsReferenceChoice : Prop :=
  IsPlanarReference R.planar ∧ R.planar.eigenvalue.im ∈ Ioo (-2 : ℝ) 0 ∧
    R.σ₀ ∈ Ioo (1 / 16 : ℝ) (1 / 8) ∧ R.planar.signedCoeff R.σ₀ ≠ 0 ∧
      ContinuousAt R.planar.mellinJ R.σ₀

/-- `r` is an admissible level choice at level `n`: it lies in the class `S n` (the common
choice of Lemma `lem:late-stress-3-10`, B0725) and meets the conclusions of Theorem B3 at
`ν = ν_n`, `P = P_n = 2ε_nc_n` (lines 5093–5141, 13714–13722, B0705). -/
def IsTrainLevel (S : ℕ → LevelChoice → Prop) (n : ℕ) (r : LevelChoice) : Prop :=
  S n r ∧ IsB3Output (R.base.ν n) (R.base.period n) r.a r.U r.Q r.p

/-- **C3** (existence form): Theorem B3 (`background:thm:B3`, lines 5093–5141, B0705) at
`ν = ν_n`, `c = ν_n^{-2}`, `R = ε_n⁻¹`, `P = 2ε_nc_n` for all large `n` (lines 13714–13722:
"Theorem B3 supplies `U = H_ν[a] + Q`, `a ≠ 0`, `Q ∈ C_per H²`"), within the common choice
`S n` of Lemma 3-10 (lines 13612–13616, B0725): there is a level choice of class `S n` that
satisfies `IsB3Output` (the datum (2.8), the periodic `𝒪`-invariant background (2.2), (2.4)
with bounded `U`, `∇U` (line 5122), (2.5) with the global pressure `p ∈ C_per L²`, and
`Q ∈ C_per H²` (2.10)). -/
def TheoremB3 (S : ℕ → LevelChoice → Prop) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ r : LevelChoice, R.IsTrainLevel S n r

/-- **C7** (existence form): for all large `n` and every admissible level choice, the
observation is admissible (`prepared:p4.2`–`p4.3`, lines 9542–9563, B0596) and at every `σ`
of the window the full reduced matrix exists: the pencil `A_σ` is invertible and `B_full(σ)`
is the lower-right block of its inverse (`eq:m4-inverse-blocks`, lines 9738–9750, B0747;
the exact correspondence `eq:st18-t00631`–`t00632`, lines 10870–10889, B0770, B0771; "The
common choice supplies the ordinary and gain near inverses ... Section 12887 therefore makes
the full reduced matrix real and continuous on this interval", lines 13653–13656, B1000;
lines 13680–13692, B1004), for the explicit inlet column of the prepared vorticity
(lines 9139–9232). -/
def ReducedMatrixExists (S : ℕ → LevelChoice → Prop) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ r : LevelChoice, R.IsTrainLevel S n r →
    IsAdmissibleObservation (R.base.spacing n) r.observation ∧
      ∀ σ ∈ R.base.window n, ∃ B : Matrix2, IsReducedMatrix (R.base.ν n) (R.base.radius n)
        (R.base.period n) σ r.U (R.base.inletStreams n) r.observation B

/-- **C6** (existence form): `prop:uniform-reduced-return` (lines 13377–13422, B0992, with
`eq:st18-t00762`) on the window, read as at lines 13653–13660 (B1000). For admissible level
choices `r n` and any full reduced matrices `B n σ` of them on the window (`IsReducedMatrix`
determines `B_full` given the background and the observation, `Cylinder.lean`), there is a
normalizer `G` (the manuscript's exact Gram `G_H = C_HΦ_σ`, invertible by
`prepared:p4.10`–`p4.11`, with `B_fullG_H` continuous by Section `sec:st18-12887`) with
`det G ≠ 0` and `BG` continuous on the window, and `BG = I - K₀ + o(1)` uniformly on the
window. The window lies in the gain band and in `K` for large `n` (t00765, lines
13648–13650), where the proposition applies. -/
def UniformReducedReturn (S : ℕ → LevelChoice → Prop) : Prop :=
  ∀ (r : ℕ → LevelChoice) (B : ℕ → ℝ → Matrix2),
    (∀ᶠ n : ℕ in atTop, R.IsTrainLevel S n (r n) ∧
      IsAdmissibleObservation (R.base.spacing n) (r n).observation ∧
      ∀ σ ∈ R.base.window n, IsReducedMatrix (R.base.ν n) (R.base.radius n) (R.base.period n)
        σ (r n).U (R.base.inletStreams n) (r n).observation (B n σ)) →
    ∃ G : ℕ → ℝ → Matrix2,
      (∀ᶠ n : ℕ in atTop, ContinuousOn (fun σ => B n σ * G n σ) (R.base.window n) ∧
        ∀ σ ∈ R.base.window n, (G n σ).det ≠ 0) ∧
      ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ σ ∈ R.base.window n, ∀ i j,
        |(B n σ * G n σ - (1 - R.base.K0 n σ)) i j| ≤ δ

/-! ## The record -/

open Classical in
/-- The level choice at level `n`: `Classical.choose` of `TheoremB3` where it holds, a
placeholder elsewhere (no statement is made at those finitely many levels). -/
def levelChoice (S : ℕ → LevelChoice → Prop) (n : ℕ) : LevelChoice :=
  if h : ∃ r : LevelChoice, R.IsTrainLevel S n r then Classical.choose h else LevelChoice.zero

open Classical in
/-- `B_full(σ)` at level `n` for the chosen background and observation: `Classical.choose`
of `ReducedMatrixExists` where it holds, `0` elsewhere. -/
def reducedMatrix (S : ℕ → LevelChoice → Prop) (n : ℕ) (σ : ℝ) : Matrix2 :=
  if h : ∃ B : Matrix2, IsReducedMatrix (R.base.ν n) (R.base.radius n) (R.base.period n) σ
      (R.levelChoice S n).U (R.base.inletStreams n) (R.levelChoice S n).observation B
  then Classical.choose h else 0

/-- **The construction data of the final theorem** (lines 13608–13745): the reference `R`,
the phase-locked viscosities `ν_n` (t00763), and at each level the background, datum,
remainder, pressure and observation of Theorem B3 with the common choice, and the full
reduced matrix `B_full(σ)` (t00766). -/
def data (S : ℕ → LevelChoice → Prop) : ConstructionData where
  planar := R.planar
  σ₀ := R.σ₀
  ν := R.base.ν
  a n := (R.levelChoice S n).a
  U n := (R.levelChoice S n).U
  Q n := (R.levelChoice S n).Q
  p n := (R.levelChoice S n).p
  observation n := (R.levelChoice S n).observation
  Bfull := R.reducedMatrix S

variable (S : ℕ → LevelChoice → Prop)

/-! The explicit quantities of `data` do not depend on the class `S`. -/

theorem data_ν : (R.data S).ν = R.base.ν := rfl

theorem data_ν_eq_phaseLockedNu : (R.data S).ν = (R.data S).phaseLockedNu := rfl

theorem data_period : (R.data S).period = R.base.period := rfl

theorem data_spacing : (R.data S).spacing = R.base.spacing := rfl

theorem data_radius : (R.data S).radius = R.base.radius := rfl

theorem data_window : (R.data S).window = R.base.window := rfl

theorem data_K0 : (R.data S).K0 = R.base.K0 := rfl

theorem data_inletStreams : (R.data S).inletStreams = R.base.inletStreams := rfl

/-- C1 for the record is C1 for its reference. -/
theorem stepReferenceChoice_data : StepReferenceChoice (R.data S) ↔ R.IsReferenceChoice :=
  Iff.rfl

variable {R S}

theorem levelChoice_spec {n : ℕ} (h : ∃ r : LevelChoice, R.IsTrainLevel S n r) :
    R.IsTrainLevel S n (R.levelChoice S n) := by
  unfold levelChoice
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem reducedMatrix_spec {n : ℕ} {σ : ℝ}
    (h : ∃ B : Matrix2, IsReducedMatrix (R.base.ν n) (R.base.radius n) (R.base.period n) σ
      (R.levelChoice S n).U (R.base.inletStreams n) (R.levelChoice S n).observation B) :
    IsReducedMatrix (R.base.ν n) (R.base.radius n) (R.base.period n) σ
      (R.levelChoice S n).U (R.base.inletStreams n) (R.levelChoice S n).observation
      (R.reducedMatrix S n σ) := by
  unfold reducedMatrix
  rw [dite_eq_left h]
  exact Classical.choose_spec h

/-! ## The steps for the record -/

/-- **C2** for the record (`eq:st18-t00763`, lines 13618–13626, B0997), from C1, by the proved
`ConstructionData.stepPhaseLocked_of_C1` (`Cons/C02PhaseLocked.lean`). -/
theorem stepPhaseLocked_data (h1 : R.IsReferenceChoice) : StepPhaseLocked (R.data S) :=
  ConstructionData.stepPhaseLocked_of_C1 ((stepReferenceChoice_data R S).2 h1)
    (data_ν_eq_phaseLockedNu R S)

/-- **C3** for the record (lines 13714–13722, B0705), from Theorem B3. -/
theorem stepBackground_data (h3 : R.TheoremB3 S) : StepBackground (R.data S) := by
  filter_upwards [h3] with n hn
  exact (levelChoice_spec hn).2

/-- The chosen level and the reduced matrices are admissible for all large `n`. -/
theorem eventually_reduced (h3 : R.TheoremB3 S) (h7 : R.ReducedMatrixExists S) :
    ∀ᶠ n : ℕ in atTop, R.IsTrainLevel S n (R.levelChoice S n) ∧
      IsAdmissibleObservation (R.base.spacing n) (R.levelChoice S n).observation ∧
      ∀ σ ∈ R.base.window n, IsReducedMatrix (R.base.ν n) (R.base.radius n)
        (R.base.period n) σ (R.levelChoice S n).U (R.base.inletStreams n)
        (R.levelChoice S n).observation (R.reducedMatrix S n σ) := by
  filter_upwards [h3, h7] with n h3n h7n
  have hl := levelChoice_spec h3n
  obtain ⟨hadm, hB⟩ := h7n _ hl
  exact ⟨hl, hadm, fun σ hσ => reducedMatrix_spec (hB σ hσ)⟩

/-- **C7** for the record (lines 13653–13656, 13680–13692, B1004), from Theorem B3 and the
existence of the reduced matrix. -/
theorem stepReducedMatrix_data (h3 : R.TheoremB3 S) (h7 : R.ReducedMatrixExists S) :
    StepReducedMatrix (R.data S) := by
  filter_upwards [eventually_reduced h3 h7] with n hn
  exact hn.2

/-- **C6** for the record (lines 13653–13660, B0992, B1000), from Theorem B3, the existence of
the reduced matrix and `prop:uniform-reduced-return`. -/
theorem stepUniformReturn_data (h3 : R.TheoremB3 S) (h6 : R.UniformReducedReturn S)
    (h7 : R.ReducedMatrixExists S) : StepUniformReturn (R.data S) :=
  h6 (R.levelChoice S) (R.reducedMatrix S) (eventually_reduced h3 h7)

/-- The data-dependent steps C1, C2, C3, C6, C7 for the record `R.data S`. -/
theorem constructionSteps_data (h1 : R.IsReferenceChoice) (h3 : R.TheoremB3 S)
    (h6 : R.UniformReducedReturn S) (h7 : R.ReducedMatrixExists S) :
    StepReferenceChoice (R.data S) ∧ StepPhaseLocked (R.data S) ∧ StepBackground (R.data S) ∧
      StepUniformReturn (R.data S) ∧ StepReducedMatrix (R.data S) :=
  ⟨(stepReferenceChoice_data R S).2 h1, stepPhaseLocked_data h1, stepBackground_data h3,
    stepUniformReturn_data h3 h6 h7, stepReducedMatrix_data h3 h7⟩

/-- `ConstructionSteps` (`Compose.lean`) from C1, C3, C6, C7 for one reference and class. -/
theorem constructionSteps (h1 : R.IsReferenceChoice) (h3 : R.TheoremB3 S)
    (h6 : R.UniformReducedReturn S) (h7 : R.ReducedMatrixExists S) : ConstructionSteps :=
  ⟨R.data S, constructionSteps_data h1 h3 h6 h7⟩

end Reference

/-! ## `ConstructionClaim` from the existence statements -/

/-- **C1** (existence form): some reference meets G1–G4, `-2 < ω < 0` and the choice
`μ₀ ∈ (1/16,1/8)` with `𝒞(μ₀) ≠ 0` and `𝓙` continuous at `μ₀` (lines 691–800, 696,
13196–13213; B0085, B0882). -/
def ReferenceChoiceExists : Prop :=
  ∃ R : Reference, R.IsReferenceChoice

/-- `prop:unstable-background` (B1034) from C1, C3, C6, C7 for one explicit reference `R` and
class `S`, and C8. C2, C4, C5 and C9 are discharged by proved theorems. -/
theorem constructionClaim_of_reference (R : Reference) (S : ℕ → LevelChoice → Prop)
    (h1 : R.IsReferenceChoice) (h3 : R.TheoremB3 S) (h6 : R.UniformReducedReturn S)
    (h7 : R.ReducedMatrixExists S) (h8 : StepPhysicalMode) : ConstructionClaim := by
  obtain ⟨h1', h2, h3', h6', h7'⟩ := Reference.constructionSteps_data h1 h3 h6 h7
  exact constructionClaim_of_steps (R.data S) h1' h2 h3' h6' h7' h8 pressureProjectionStep

/-- The reference chosen from C1. -/
def chosenReference (hE1 : ReferenceChoiceExists) : Reference := Classical.choose hE1

theorem chosenReference_spec (hE1 : ReferenceChoiceExists) :
    (chosenReference hE1).IsReferenceChoice :=
  Classical.choose_spec hE1

/-- **The concrete `ConstructionData` of the final theorem**: the reference chosen from C1,
the phase-locked sequence of C2, and the level choices and reduced matrices chosen from C3 and
C7 within the class `S` of that reference. -/
def constructionData (hE1 : ReferenceChoiceExists) (S : Reference → ℕ → LevelChoice → Prop) :
    ConstructionData :=
  (chosenReference hE1).data (S (chosenReference hE1))

/-- **`prop:unstable-background`** (lines 150–191, B1034; completion, lines 13714–13745,
B1033) from the existence statements, with the reference chosen from C1 (`constructionData`):
* `hE1` C1: G1–G4, `-2 < ω < 0`, `𝒞(μ₀) ≠ 0` (lines 691–800, 13196–13213; B0085, B0882);
* `hE3` C3: Theorem B3 at `(ν_n, P_n)` within the common choice (lines 5093–5141,
  13714–13722; B0705, B0725);
* `hE6` C6: `prop:uniform-reduced-return` on the window (lines 13377–13422, 13653–13660;
  B0992, B1000);
* `hE7` C7: the full reduced matrix (lines 9738–9750, 10870–10889, 13653–13656,
  13680–13692; B0747, B0770, B0771, B1004);
* `hE8` C8: the weak-to-body upgrade (lines 10900–10911, 13693–13707; B0773, B1005, B1006).
C3, C6, C7 are asked for every reference meeting C1, since the chosen one is arbitrary
(`constructionClaim_of_reference` asks them for one reference only). -/
theorem constructionClaim_of_existence (hE1 : ReferenceChoiceExists)
    (S : Reference → ℕ → LevelChoice → Prop)
    (hE3 : ∀ R : Reference, R.IsReferenceChoice → R.TheoremB3 (S R))
    (hE6 : ∀ R : Reference, R.IsReferenceChoice → R.UniformReducedReturn (S R))
    (hE7 : ∀ R : Reference, R.IsReferenceChoice → R.ReducedMatrixExists (S R))
    (hE8 : StepPhysicalMode) : ConstructionClaim :=
  have h1 := chosenReference_spec hE1
  constructionClaim_of_reference (chosenReference hE1) (S (chosenReference hE1)) h1
    (hE3 _ h1) (hE6 _ h1) (hE7 _ h1) hE8

/-- The data-dependent existence statements C1, C3, C6, C7 as one proposition, in the weakest
form: some reference and some class of level choices satisfy them. The manuscript proves it
with its reference and the common choice of Lemma 3-10 (lines 13608–13616, 13714–13725). -/
def ConstructionExistence : Prop :=
  ∃ R : Reference, R.IsReferenceChoice ∧ ∃ S : ℕ → LevelChoice → Prop,
    R.TheoremB3 S ∧ R.UniformReducedReturn S ∧ R.ReducedMatrixExists S

/-- `prop:unstable-background` from `ConstructionExistence` and C8. -/
theorem constructionClaim_of_constructionExistence (h : ConstructionExistence)
    (hE8 : StepPhysicalMode) : ConstructionClaim := by
  obtain ⟨R, h1, S, h3, h6, h7⟩ := h
  exact constructionClaim_of_reference R S h1 h3 h6 h7 hE8

/-- `ConstructionExistence` gives `ConstructionSteps` (`Compose.lean`). -/
theorem constructionSteps_of_constructionExistence (h : ConstructionExistence) :
    ConstructionSteps := by
  obtain ⟨R, h1, S, h3, h6, h7⟩ := h
  exact Reference.constructionSteps h1 h3 h6 h7

/-- **Theorem A** (`MainClaim`, lines 74–105) from `ConstructionExistence` and C8, by the
compiled localization half (`Loc/AssemblyB.lean`, `mainClaim_of_constructionClaim`). -/
theorem mainClaim_of_constructionExistence (h : ConstructionExistence)
    (hE8 : StepPhysicalMode) : MainClaim :=
  Loc.Assembly.mainClaim_of_constructionClaim (constructionClaim_of_constructionExistence h hE8)

/-- **Theorem A** from the existence statements of `constructionClaim_of_existence`. -/
theorem mainClaim_of_existence (hE1 : ReferenceChoiceExists)
    (S : Reference → ℕ → LevelChoice → Prop)
    (hE3 : ∀ R : Reference, R.IsReferenceChoice → R.TheoremB3 (S R))
    (hE6 : ∀ R : Reference, R.IsReferenceChoice → R.UniformReducedReturn (S R))
    (hE7 : ∀ R : Reference, R.IsReferenceChoice → R.ReducedMatrixExists (S R))
    (hE8 : StepPhysicalMode) : MainClaim :=
  Loc.Assembly.mainClaim_of_constructionClaim
    (constructionClaim_of_existence hE1 S hE3 hE6 hE7 hE8)

end UnforcedLeray.Cons.Data

#print axioms UnforcedLeray.Cons.Data.constructionClaim_of_reference
#print axioms UnforcedLeray.Cons.Data.constructionClaim_of_existence
#print axioms UnforcedLeray.Cons.Data.constructionClaim_of_constructionExistence
#print axioms UnforcedLeray.Cons.Data.mainClaim_of_existence
#print axioms UnforcedLeray.Cons.Data.mainClaim_of_constructionExistence
