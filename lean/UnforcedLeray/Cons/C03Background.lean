import UnforcedLeray.Cons.C03Background.Scheme
import UnforcedLeray.Cons.C03Background.Parameters
import UnforcedLeray.Cons.C02PhaseLocked
import UnforcedLeray.Cons.C09PressureProjection
import UnforcedLeray.Blueprint.Construction.Compose

/-!
# Step C3′ (and C3): the exact common unforced background, Theorem B3

Target: `StepBackgroundProjected` (C3′, preferred) and `StepBackground` (C3) of
`Blueprint/Construction/Steps.lean`: Theorem B3 (`background:thm:B3`, `paper/main.tex`
lines 5093–5141, unit B0705) at `ν = ν_n`, `P = P_n = 2ε_nc_n` for all large `n`, as used at
the completion (lines 13714–13725: "Fix one sufficiently large member … with `ν = ν_n`,
`c = ν⁻²`, `R = ε⁻¹` and `P = 2εc`. The common choice includes (2.41)–(2.43) …
Theorem B3 supplies `U = U_raw + E_bgα_bg + w_bg = H_ν[a] + Q`").

## The record

C3 constrains the fields `a`, `U`, `Q` (and `p`) of a `ConstructionData`, which are free in the
record, so C3 cannot hold for every record (as for C2, `Cons/C02PhaseLocked.lean`).
`F.withB3` replaces `a`, `U`, `Q` at level `n` by a choice of Theorem B3's projected output at
`(ν_n, P_n)` when it exists (and keeps `F`'s fields otherwise); `F.withB3Literal` does the
same with `p` for the literal output. `planar`, `σ₀`, `ν`, `observation`, `Bfull` are those of
`F`, so C1 and C2 are unchanged (`stepReferenceChoice_withB3`, `stepPhaseLocked_withB3`).
* `ConstructionData.stepBackgroundProjected_withB3`: C3′ for `F.withB3` as soon as Theorem B3
  (projected form) holds at `(ν_n, P_n)` for all large `n`;
  `ConstructionData.stepBackground_withB3Literal` likewise for C3.

## Theorem B3 from its ingredients (top-down)

`Cons/C03Background/Scheme.lean` proves Theorem B3 at one parameter point from the frozen
objects of its proof (`BackgroundScheme`: the train, `U_raw`, the inlet columns, the spaces
`Z = X_{q₀} × ℝ²` and `Y_{q₀}`, the augmented inverse, the ordinary operator, the quadratic
source, the raw residual, the symmetric class, the datum) and named hypotheses, each one
manuscript result (`SchemeHyps`, `ProjectedEquationHyp` below). Proved along the way:
* the nonlinear closure (2.43) with the symmetric class (`Contraction.lean`; B0685, B0688), with
  the manuscript's exact condition `4PM²δ < 1`;
* the smallness `4PM²δ < 1` for all large `n` at the construction's `ε_n`, `c_n = ν_n⁻²`, from
  `22m < γ` (`Parameters.lean`; B0685 with Lemma 3-10, B0725);
* the zero projected residual at the fixed point from the ordinary solve and the residual
  expansion (`zeroResidualHyp_of_expansion`; B0701);
* the `c`-periodicity of the train's decaying stream and of the raw profile, and the
  `P`-periodicity and `𝒪`-invariance of `U_raw` and of the inlet columns from the ring lift
  (`RawLift.lean`, `Pieces.lean`; B0186, with the compiled `Axi.Nv`, `Axi.chart_add_period`,
  `Axi.isAxisymmetricNoSwirl_Nv` and the train unit B0140);
* the background clauses of B3 for the sum `U = U_raw + E_bgα + w_bg` (`Pieces.lean`);
* the datum's global solenoidality from its pointwise divergence off `0` and `|a| ≤ C|x|⁻¹`
  (`IsB3DatumOffZero.toIsB3Datum`, with the compiled AX07; B0687);
* the projected equation from the literal (2.5) with pressure, by the compiled C9
  (`zeroResidualHyp_of_pressureHyp`; B0708).

**Main theorems.**
* `stepBackgroundProjected_of_hyps` (C3′ for `F.withB3`) and `stepBackground_of_hyps`
  (C3 for `F.withB3Literal`): for a record with `ν_n > 0`, `ν_n → 0`, `C₀ ≠ 0` and a budget
  `B = (C, k, m)` with `22m < γ`, from `BackgroundHyps F B` (resp. `BackgroundHypsLiteral F B`):
  for all large `n` there is a scheme at `(ν_n, c_n)` meeting `SchemeHyps` and
  `ProjectedEquationHyp` (resp. `PressureHyp`) at `ε_n`.
* `stepBackgroundProjected_of_literalHyps`: C3′ from the literal hypotheses (through C9).
* `stepBackgroundProjected_of_C1_C2`: C3′ from C1, C2 and `BackgroundHyps`.
* `steps_withPhaseLocked_withB3`: C1, C2 and C3′ together for `F.withPhaseLocked.withB3`, from
  C1 for `F` and `BackgroundHyps` (C2 is the compiled `Cons/C02PhaseLocked.lean`).
* `constructionClaim_of_background_schemes`: `ConstructionClaim` from C1, `BackgroundHyps`,
  C6 and C7 for that record, and C8 (the composition of `Construction/Compose.lean`).

## What remains (the named hypotheses)

For all large `n`, a scheme at `(ν_n, c_n = ν_n⁻²)`, with `ε = ε_n`, `R = ε_n⁻¹`,
`P = P_n = 2ε_nc_n`, and one budget `(C, k, m)` with `22m < γ` for all `n`:

| Hypothesis | Manuscript | Units |
|---|---|---|
| the train `TrainSol ν_n c_n` (a field of the scheme) | lines 2045–2057, 2141–2161 | B0140, B0141 (`TrainIVPSolvable`) |
| `RawLiftHyp` | (2.15), `eq:m3-ring-lift`, lines 2070–2098, 5197–5205, 5831–5850 | B0282, B0186, B0189, B0200, B0695 |
| `InletHyp` | `eq:m2-background-inlet`, (2.26)–(2.28) | B0303, B0297, B0298, B0299 |
| `InverseBoundHyp` | (2.31) (with (2.33)–(2.40n), (2.41)) | B0684, B0682, B0683 |
| `OrdinarySolveHyp` | `eq:m3-ordinary-system`, (2.31)–(2.32) | B0684 |
| `QuadraticBoundHyp` | (2.42) | B0458 |
| `RawResidualHyp` | (2.15) | B0282, B0200 |
| `SymmetricClassHyp` | `unlabeled:5725`, (2.2) | B0688, B0416 |
| `CorrectionClassHyp` | (2.3) with (2.2) | B0412, B0416, B0688 |
| `CorrectionBoundsHyp` | (2.7), (2.44)–(2.46), `unlabeled:5831` | B0692, B0689–B0691, B0695 |
| `ResidualExpansionHyp` (C3′) or `PressureHyp` (C3) | (2.44) with (2.15); (2.5), `unlabeled:5995` | B0689, B0282, B0701; B0701, B0700 |
| `DatumHyp` | (2.8) | B0687 |
| `HeatRemainderHyp` | (2.10), (2.48)–(2.51) | B0704, B0703 |

The inlet columns, the datum and the spaces are characterized structurally (as the
observation is in C7): a scheme that met the hypotheses with other objects would still give a
genuine `IsB3ProjectedOutput`, since the conclusion is literal.

Status: the assembly compiles with the standard axioms only; the hypotheses above are OPEN, so
C3′ and C3 are not proved. Theorem A is not proved.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Cons.C03

open UnforcedLeray.Blueprint

/-! ## Theorem B3 at one point, as a proposition -/

/-- Theorem B3's projected output exists at `(ν, P)` (`IsB3ProjectedOutput`). -/
def B3ProjectedAt (ν P : ℝ) : Prop :=
  ∃ x : SpatialField × (ℝ → SpatialField) × (ℝ → SobolevGraph.H2),
    IsB3ProjectedOutput ν P x.1 x.2.1 x.2.2

/-- Theorem B3's literal output, with the global pressure, exists at `(ν, P)` (`IsB3Output`). -/
def B3At (ν P : ℝ) : Prop :=
  ∃ x : SpatialField × (ℝ → SpatialField) × (ℝ → SobolevGraph.H2) × (ℝ → Space → ℝ),
    IsB3Output ν P x.1 x.2.1 x.2.2.1 x.2.2.2

theorem B3At.toProjected {ν P : ℝ} (h : B3At ν P) : B3ProjectedAt ν P := by
  obtain ⟨x, hx⟩ := h
  exact ⟨(x.1, x.2.1, x.2.2.1), hx.toProjected pressureProjectionStep⟩

end UnforcedLeray.Cons.C03

/-! ## The record with Theorem B3's background -/

namespace UnforcedLeray.Blueprint.ConstructionData

open UnforcedLeray.Cons.C03

variable (F : ConstructionData)

open Classical in
/-- `F` with `a`, `U`, `Q` at level `n` replaced by a choice of Theorem B3's projected output
at `(ν_n, P_n)` when it exists (and kept otherwise). All other fields are those of `F`. -/
def withB3 : ConstructionData :=
  { F with
    a := fun n => if h : B3ProjectedAt (F.ν n) (F.period n) then h.choose.1 else F.a n
    U := fun n => if h : B3ProjectedAt (F.ν n) (F.period n) then h.choose.2.1 else F.U n
    Q := fun n => if h : B3ProjectedAt (F.ν n) (F.period n) then h.choose.2.2 else F.Q n }

open Classical in
/-- `F` with `a`, `U`, `Q`, `p` at level `n` replaced by a choice of Theorem B3's literal
output at `(ν_n, P_n)` when it exists (and kept otherwise). -/
def withB3Literal : ConstructionData :=
  { F with
    a := fun n => if h : B3At (F.ν n) (F.period n) then h.choose.1 else F.a n
    U := fun n => if h : B3At (F.ν n) (F.period n) then h.choose.2.1 else F.U n
    Q := fun n => if h : B3At (F.ν n) (F.period n) then h.choose.2.2.1 else F.Q n
    p := fun n => if h : B3At (F.ν n) (F.period n) then h.choose.2.2.2 else F.p n }

@[simp] theorem withB3_planar : (withB3 F).planar = F.planar := rfl
@[simp] theorem withB3_σ₀ : (withB3 F).σ₀ = F.σ₀ := rfl
@[simp] theorem withB3_ν : (withB3 F).ν = F.ν := rfl
@[simp] theorem withB3_observation : (withB3 F).observation = F.observation := rfl
@[simp] theorem withB3_Bfull : (withB3 F).Bfull = F.Bfull := rfl
theorem withB3_period : (withB3 F).period = F.period := rfl
theorem withB3Literal_period : (withB3Literal F).period = F.period := rfl

/-- C1 does not involve the background fields. -/
theorem stepReferenceChoice_withB3 : StepReferenceChoice (withB3 F) ↔ StepReferenceChoice F :=
  Iff.rfl

/-- C2 does not involve the background fields. -/
theorem stepPhaseLocked_withB3 : StepPhaseLocked (withB3 F) ↔ StepPhaseLocked F := Iff.rfl

theorem stepReferenceChoice_withB3Literal :
    StepReferenceChoice (withB3Literal F) ↔ StepReferenceChoice F := Iff.rfl

theorem stepPhaseLocked_withB3Literal :
    StepPhaseLocked (withB3Literal F) ↔ StepPhaseLocked F := Iff.rfl

variable {F}

/-- **C3′ for `F.withB3`**, as soon as Theorem B3 (projected form) holds at `(ν_n, P_n)` for
all large `n` (lines 13714–13725). -/
theorem stepBackgroundProjected_withB3
    (h : ∀ᶠ n in atTop, B3ProjectedAt (F.ν n) (F.period n)) :
    StepBackgroundProjected (withB3 F) := by
  filter_upwards [h] with n hn
  show IsB3ProjectedOutput (F.ν n) (F.period n) ((withB3 F).a n) ((withB3 F).U n)
    ((withB3 F).Q n)
  simp only [withB3, dite_eq_left hn]
  exact hn.choose_spec

/-- **C3 for `F.withB3Literal`**, as soon as Theorem B3 (literal form) holds at `(ν_n, P_n)`
for all large `n`. -/
theorem stepBackground_withB3Literal (h : ∀ᶠ n in atTop, B3At (F.ν n) (F.period n)) :
    StepBackground (withB3Literal F) := by
  filter_upwards [h] with n hn
  show IsB3Output (F.ν n) (F.period n) ((withB3Literal F).a n) ((withB3Literal F).U n)
    ((withB3Literal F).Q n) ((withB3Literal F).p n)
  simp only [withB3Literal, dite_eq_left hn]
  exact hn.choose_spec

end UnforcedLeray.Blueprint.ConstructionData

namespace UnforcedLeray.Cons.C03

open UnforcedLeray.Blueprint

/-! ## The pressure route (C9) -/

/-- The literal (2.5) with an `L²` pressure gives the projected equation, by the compiled C9
(`Cons/C09PressureProjection.lean`, `pressureProjectionStep`). -/
theorem zeroResidualHyp_of_pressureHyp {ν c ε ρ : ℝ} {S : BackgroundScheme ν c} (hε : ε ≠ 0)
    (hraw : RawLiftHyp S ε) (hin : InletHyp S ε c) (hcorr : CorrectionHyp S (2 * ε * c) ρ)
    (h : PressureHyp S ρ) : ZeroResidualHyp S ρ := by
  intro z hz
  obtain ⟨p, hp, hT, hpL2⟩ := h z hz
  exact pressureProjectionStep ν (S.field z) p
    (S.isBackgroundPiece_field hε hraw hin hcorr hz).solenoidal hT hpL2 hp

/-! ## Theorem B3 along the sequence, from the named hypotheses -/

/-- `ε_n > 0` for `ν_n > 0` and `C₀ ≠ 0`. -/
theorem amplitude_pos_of {F : ConstructionData} (hC : F.C₀ ≠ 0) {n : ℕ} (hν : 0 < F.ν n) :
    0 < F.amplitude n := by
  unfold ConstructionData.amplitude
  apply Real.rpow_pos_of_pos
  have hC' : 0 < ‖F.C₀‖ := norm_pos_iff.mpr hC
  have := Real.exp_pos (-(F.growth / F.ν n))
  have := Real.rpow_pos_of_pos hν (F.κ.re - 5 - 2 * F.σ₀)
  positivity

/-- **The named hypotheses of Theorem B3 for one scheme** at viscosity `ν`, train period `c`,
ring parameter `ε` (`R = ε⁻¹`, `P = 2εc`) and budget `B = (C, k, m)`: `M = Cν^{-k}e^{m/ν}`,
`P_ν = Cν^{-k}`, `δ = Cν^{-k}ε^{3/11}`, contraction radius `2Mδ`. Each field is one
manuscript result (see `Scheme.lean`). The equation hypotheses are separate
(`ProjectedEquationHyp`, or `PressureHyp`). -/
structure SchemeHyps {ν c : ℝ} (S : BackgroundScheme ν c) (B : Budget) (ε : ℝ) : Prop where
  /-- (2.15), `eq:m3-ring-lift` (B0282, B0186, B0189, B0695). -/
  rawLift : RawLiftHyp S ε
  /-- `eq:m2-background-inlet`, (2.26)–(2.28) (B0303, B0297–B0299). -/
  inlet : InletHyp S ε c
  /-- (2.31) (B0684, B0682, B0683). -/
  inverse : InverseBoundHyp S (B.loss ν)
  /-- (2.42) (B0458). -/
  quadratic : QuadraticBoundHyp S (B.poly ν)
  /-- (2.15) (B0282, B0200). -/
  rawResidual : RawResidualHyp S (B.residual ν ε)
  /-- `unlabeled:5725`, (2.2) (B0688, B0416). -/
  symClass : SymmetricClassHyp S (B.radius ν ε)
  /-- (2.3) with (2.2) (B0412, B0416, B0688). -/
  correctionClass : CorrectionClassHyp S (2 * ε * c) (B.radius ν ε)
  /-- (2.7), (2.44)–(2.46), `unlabeled:5831` (B0692, B0689–B0691, B0695). -/
  correctionBounds : CorrectionBoundsHyp S (B.radius ν ε)
  /-- (2.8) (B0687). -/
  datum : DatumHyp S (2 * ε * c) (B.radius ν ε)
  /-- (2.10), (2.48)–(2.51) (B0704, B0703). -/
  remainder : HeatRemainderHyp S (2 * ε * c) (B.radius ν ε)

/-- **The projected equation hypotheses for one scheme**: the ordinary inverse solves the
ordinary system (`eq:m3-ordinary-system`, B0684) and the residual expansion
(`background:eq:2.44` with (2.15), B0689, B0282, B0701). -/
structure ProjectedEquationHyp {ν c : ℝ} (S : BackgroundScheme ν c) (B : Budget) (ε : ℝ) :
    Prop where
  solve : OrdinarySolveHyp S
  expansion : ResidualExpansionHyp S (B.radius ν ε)

/-- **Theorem B3, projected form, at one parameter point, from the named hypotheses** and the
smallness `4PM²δ < 1` of (2.43). -/
theorem b3ProjectedAt_of_hyps {ν c ε : ℝ} (hε : ε ≠ 0) {S : BackgroundScheme ν c}
    {B : Budget} (H : SchemeHyps S B ε) (heq : ZeroResidualHyp S (B.radius ν ε))
    (hsmall : B.smallness ν ε < 1) : B3ProjectedAt ν (2 * ε * c) := by
  obtain ⟨a, U, Q, hB⟩ := S.b3Projected_of_scheme hε H.rawLift H.inlet H.inverse H.quadratic
    H.rawResidual hsmall H.symClass (correctionHyp_of S H.correctionClass H.correctionBounds)
    heq H.datum H.remainder
  exact ⟨(a, U, Q), hB⟩

/-- **Theorem B3, literal form, at one parameter point, from the named hypotheses** with
`PressureHyp` and the smallness `4PM²δ < 1` of (2.43). -/
theorem b3At_of_hyps {ν c ε : ℝ} (hε : ε ≠ 0) {S : BackgroundScheme ν c} {B : Budget}
    (H : SchemeHyps S B ε) (hpr : PressureHyp S (B.radius ν ε))
    (hsmall : B.smallness ν ε < 1) : B3At ν (2 * ε * c) := by
  obtain ⟨a, U, Q, p, hB⟩ := S.b3_of_scheme hε H.rawLift H.inlet H.inverse H.quadratic
    H.rawResidual hsmall H.symClass (correctionHyp_of S H.correctionClass H.correctionBounds)
    hpr H.datum H.remainder
  exact ⟨(a, U, Q, p), hB⟩

/-- **The background hypotheses along the sequence** (lines 5093–6003, 13714–13725): for all
large `n` there is a scheme at `(ν_n, c_n = ν_n⁻²)` meeting the named hypotheses of Theorem B3
at `ε = ε_n` and the projected equation hypotheses. -/
def BackgroundHyps (F : ConstructionData) (B : Budget) : Prop :=
  ∀ᶠ n in atTop, ∃ S : BackgroundScheme (F.ν n) (F.spacing n),
    SchemeHyps S B (F.amplitude n) ∧ ProjectedEquationHyp S B (F.amplitude n)

/-- **The background hypotheses along the sequence, literal form**: as `BackgroundHyps`, with
`PressureHyp` in place of the projected equation hypotheses. -/
def BackgroundHypsLiteral (F : ConstructionData) (B : Budget) : Prop :=
  ∀ᶠ n in atTop, ∃ S : BackgroundScheme (F.ν n) (F.spacing n),
    SchemeHyps S B (F.amplitude n) ∧ PressureHyp S (B.radius (F.ν n) (F.amplitude n))

/-- **Theorem B3 (projected form) for all large `n`**, from the named hypotheses: the
smallness of (2.43) holds for large `n` (`eventually_smallness`, from `22m < γ`). -/
theorem eventually_b3ProjectedAt {F : ConstructionData} (hν : ∀ n, 0 < F.ν n)
    (hν0 : Tendsto F.ν atTop (𝓝 0)) (hC : F.C₀ ≠ 0) {B : Budget}
    (hm : 22 * B.m < F.growth) (H : BackgroundHyps F B) :
    ∀ᶠ n in atTop, B3ProjectedAt (F.ν n) (F.period n) := by
  filter_upwards [H, eventually_smallness F hν hν0 hC B hm] with n ⟨S, hS, hE⟩ hsmall
  exact b3ProjectedAt_of_hyps (amplitude_pos_of hC (hν n)).ne' hS
    (zeroResidualHyp_of_expansion S hE.solve hE.expansion) hsmall

/-- **Theorem B3 (literal form) for all large `n`**, from the named hypotheses with
`PressureHyp`. -/
theorem eventually_b3At {F : ConstructionData} (hν : ∀ n, 0 < F.ν n)
    (hν0 : Tendsto F.ν atTop (𝓝 0)) (hC : F.C₀ ≠ 0) {B : Budget}
    (hm : 22 * B.m < F.growth) (H : BackgroundHypsLiteral F B) :
    ∀ᶠ n in atTop, B3At (F.ν n) (F.period n) := by
  filter_upwards [H, eventually_smallness F hν hν0 hC B hm] with n ⟨S, hS, hpr⟩ hsmall
  exact b3At_of_hyps (amplitude_pos_of hC (hν n)).ne' hS hpr hsmall

/-- **Step C3′** (`StepBackgroundProjected`, lines 5093–5141, 13714–13725, unit B0705) for the
record `F.withB3`, from the named hypotheses of Theorem B3 (`BackgroundHyps`) and a budget
with `22m < γ`. -/
theorem stepBackgroundProjected_of_hyps {F : ConstructionData} (hν : ∀ n, 0 < F.ν n)
    (hν0 : Tendsto F.ν atTop (𝓝 0)) (hC : F.C₀ ≠ 0) {B : Budget}
    (hm : 22 * B.m < F.growth) (H : BackgroundHyps F B) :
    StepBackgroundProjected F.withB3 :=
  ConstructionData.stepBackgroundProjected_withB3 (eventually_b3ProjectedAt hν hν0 hC hm H)

/-- **Step C3** (`StepBackground`, literal (2.5) with the pressure) for the record
`F.withB3Literal`, from `BackgroundHypsLiteral`. -/
theorem stepBackground_of_hyps {F : ConstructionData} (hν : ∀ n, 0 < F.ν n)
    (hν0 : Tendsto F.ν atTop (𝓝 0)) (hC : F.C₀ ≠ 0) {B : Budget}
    (hm : 22 * B.m < F.growth) (H : BackgroundHypsLiteral F B) :
    StepBackground F.withB3Literal :=
  ConstructionData.stepBackground_withB3Literal (eventually_b3At hν hν0 hC hm H)

/-- The literal hypotheses imply the projected ones, through the compiled C9
(`zeroResidualHyp_of_pressureHyp`); so `BackgroundHypsLiteral` also gives C3′ for
`F.withB3`. -/
theorem stepBackgroundProjected_of_literalHyps {F : ConstructionData} (hν : ∀ n, 0 < F.ν n)
    (hν0 : Tendsto F.ν atTop (𝓝 0)) (hC : F.C₀ ≠ 0) {B : Budget}
    (hm : 22 * B.m < F.growth) (H : BackgroundHypsLiteral F B) :
    StepBackgroundProjected F.withB3 := by
  refine ConstructionData.stepBackgroundProjected_withB3 ?_
  filter_upwards [H, eventually_smallness F hν hν0 hC B hm] with n ⟨S, hS, hpr⟩ hsmall
  have hε := (amplitude_pos_of hC (hν n)).ne'
  exact b3ProjectedAt_of_hyps hε hS (zeroResidualHyp_of_pressureHyp hε hS.rawLift hS.inlet
    (correctionHyp_of S hS.correctionClass hS.correctionBounds) hpr) hsmall

/-- **Step C3′ from C1 and C2** and the named hypotheses of Theorem B3. -/
theorem stepBackgroundProjected_of_C1_C2 {F : ConstructionData} (h1 : StepReferenceChoice F)
    (h2 : StepPhaseLocked F) {B : Budget} (hm : 22 * B.m < F.growth)
    (H : BackgroundHyps F B) : StepBackgroundProjected F.withB3 :=
  stepBackgroundProjected_of_hyps h2.1 h2.2.1 h1.2.2.2.1 hm H

/-! ## Composition with C1, C2 and the completion -/

/-- **C1, C2 and C3′ for one record**: for `F` with C1, the record
`G = F.withPhaseLocked.withB3` (the phase-locked viscosities of the compiled C2, then Theorem
B3's background) satisfies C1, C2 and C3′, given the named hypotheses of Theorem B3 for a
family of schemes at `(ν_n, c_n)` of `F.withPhaseLocked`. -/
theorem steps_withPhaseLocked_withB3 {F : ConstructionData} (h1 : StepReferenceChoice F)
    {B : Budget} (hm : 22 * B.m < F.growth) (H : BackgroundHyps F.withPhaseLocked B) :
    StepReferenceChoice F.withPhaseLocked.withB3 ∧ StepPhaseLocked F.withPhaseLocked.withB3 ∧
      StepBackgroundProjected F.withPhaseLocked.withB3 := by
  obtain ⟨h1', h2'⟩ := ConstructionData.stepReferenceChoice_and_stepPhaseLocked h1
  exact ⟨h1', h2', stepBackgroundProjected_of_C1_C2 h1' h2' hm H⟩

/-- **`prop:unstable-background` from C1, Theorem B3's named hypotheses, C6, C7 and C8**
(lines 13714–13745): the composition `constructionClaim_of_projected_steps` applied to the
record `F.withPhaseLocked.withB3`. C6 and C7 are about that record (its `U` is Theorem B3's
background). -/
theorem constructionClaim_of_background_schemes {F : ConstructionData}
    (h1 : StepReferenceChoice F) {B : Budget} (hm : 22 * B.m < F.growth)
    (H : BackgroundHyps F.withPhaseLocked B)
    (h6 : StepUniformReturn F.withPhaseLocked.withB3)
    (h7 : StepReducedMatrix F.withPhaseLocked.withB3)
    (h8 : StepPhysicalMode) : ConstructionClaim := by
  obtain ⟨h1', h2', h3'⟩ := steps_withPhaseLocked_withB3 h1 hm H
  exact constructionClaim_of_projected_steps _ h1' h2' h3' h6 h7 h8

end UnforcedLeray.Cons.C03

#print axioms UnforcedLeray.Blueprint.ConstructionData.stepBackgroundProjected_withB3
#print axioms UnforcedLeray.Blueprint.ConstructionData.stepBackground_withB3Literal
#print axioms UnforcedLeray.Cons.C03.stepBackgroundProjected_of_hyps
#print axioms UnforcedLeray.Cons.C03.stepBackground_of_hyps
#print axioms UnforcedLeray.Cons.C03.stepBackgroundProjected_of_literalHyps
#print axioms UnforcedLeray.Cons.C03.steps_withPhaseLocked_withB3
#print axioms UnforcedLeray.Cons.C03.constructionClaim_of_background_schemes
#print axioms UnforcedLeray.Cons.C03.zeroResidualHyp_of_pressureHyp
