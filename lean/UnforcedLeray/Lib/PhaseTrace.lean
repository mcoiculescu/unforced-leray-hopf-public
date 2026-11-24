import UnforcedLeray.Lib.PhaseTrace.Dilation
import UnforcedLeray.Lib.PhaseTrace.Lift
import UnforcedLeray.Lib.PhaseTrace.Periodize
import UnforcedLeray.Lib.PhaseTrace.ChartTest
import UnforcedLeray.Lib.PhaseTrace.Comoving
import UnforcedLeray.Lib.PhaseTrace.Trace

/-!
# Block 2F PHASE1: the comoving pullback and the strong phase trace (INF14 T6)


target INF14 T6 of the scoping note `scoping/INF11-INF14-Sobolev.md` §5.2, with the constant
`1` of INF25 bypass B25-4 (`scoping/INF15-INF17-INF25-Parabolic.md`; decision D15; checked in
`scoping/critic.md`). Built on Wave 1 blocks 1D (`Lib/BochnerTime`: T1 `HasWeakDerivTime` and
its representative, T7 measurability of operator families) and 1F (`Lib/PhaseSpace`: `Yq`,
phase tests, `phasePair`, `HasPhaseOp`, `freeGraph`).

Manuscript: `eq:free-stress-4` (tex 7389–7395) and its proof in `sec:st18-9174`
(tex 7607–7632). Blueprint unit B0434 ("every `w ∈ D_(ν,q)` has a canonical strongly
continuous `P`-periodic representative with
`sup_τ ‖w(τ)‖_{L^q} ≤ (1 + 3P/(2q)) ‖w‖_{Y_q} + P ‖T₀w‖_{Y_q}`"); consumers B0435 (tex
3653–3665), B0451, B1006 (`q = 2`).

| Module | Content |
|---|---|
| `Dilation` | `dil s g = g(e^{-s/2} ·)` on `L^q(ℝ³; E)`, `norm_dil`, `dil_dil`, `continuous_dil` |
| `Lift` | lifts `t ↦ f(t mod P)`: measurability, interval integrability, `∫_s^{s+P} ‖f‖ ≤ P ‖f‖` |
| `Periodize` | `perT`, `isPhaseTest_perT`, `driftT_perT`, `phasePair_perT` (unfolding) |
| `ChartTest` | `chartTest`, `driftT_chartTest`, `pairing_chartTest`, `exists_ell`, `eq_zero_of_ell` |
| `Comoving` | `comoving`, `comoving_hasWeakDerivTime` (T6, first half) |
| `Trace` | `phaseRep`, `phaseRep_add`, `continuous_phaseRep`, `norm_phaseRep_le` (T6, B25-4) |

Main results (this file): `phase_trace`, `phase_trace_line`, `phase_trace_unique`,
`freeGraph_strongTrace`, `freeGraph_strongTrace_manuscript`.

Hypotheses versus the manuscript. B0434 assumes `w ∈ D_(ν,q)`, `1 < q < ∞`. Here only the
drift identity `T₀w = b` in distributions (`HasPhaseOp driftT w b`, half of `freeGraph`) and
`1 ≤ q < ∞` are used; `ν` and `νΔw` play no role. The bound obtained has constant `1` on
`‖w‖_{Y_q}`, which implies the manuscript's `1 + 3P/(2q)` (`freeGraph_strongTrace_manuscript`).
Norms are those of `Yq` (normalised Haar measure on the phase circle, decision D2), so
`‖w‖ = ‖w‖_{Y_q}` and `‖b‖ = ‖T₀w‖_{Y_q}` as in tex 7316–7317.

Status: target T6 is compiled. This proves the B0434 claim in the Bochner model of decision
D2; B0434 as a blueprint unit is closed only after the audit. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.PhaseTrace

open UnforcedLeray.PhaseSpace UnforcedLeray.BochnerTime

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- **INF14 T6, phase trace** (B0434, `eq:free-stress-4`, tex 7389–7395; proof tex
7607–7632; constant `1` of B25-4). If `T₀w = b` in distributions on `Y_q`, `1 ≤ q < ∞`, then
`w` has a continuous representative on the phase circle `ℝ/Pℤ` with values in
`L^q(ℝ³; ℂ³)`, and `‖w̃(τ)‖_{L^q} ≤ ‖w‖_{Y_q} + P ‖b‖_{Y_q}` for every phase `τ`. -/
theorem phase_trace (hq : q ≠ ⊤) {w b : Yq P q} (h : HasPhaseOp driftT w b) :
    ∃ w' : C(AddCircle P, Lp CVec3 q (volume : Measure Space)),
      (w : AddCircle P → Lp CVec3 q (volume : Measure Space)) =ᵐ[AddCircle.haarAddCircle] w' ∧
        ∀ τ, ‖w' τ‖ ≤ ‖w‖ + P * ‖b‖ := by
  refine ⟨phaseRepC hq h, phaseRepC_ae hq h, fun τ => ?_⟩
  obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective τ
  exact norm_phaseRep_le hq h τ

/-- **T6, form on the line.** The representative as a continuous `P`-periodic map
`ℝ → L^q(ℝ³; ℂ³)` that agrees with `τ ↦ w(τ mod P)` for a.e. `τ ∈ ℝ`. -/
theorem phase_trace_line (hq : q ≠ ⊤) {w b : Yq P q} (h : HasPhaseOp driftT w b) :
    ∃ w' : ℝ → Lp CVec3 q (volume : Measure Space), Continuous w' ∧ Function.Periodic w' P ∧
      (∀ᵐ τ : ℝ ∂volume, w' τ = w (τ : AddCircle P)) ∧ ∀ τ, ‖w' τ‖ ≤ ‖w‖ + P * ‖b‖ :=
  ⟨phaseRep hq h, continuous_phaseRep hq h, phaseRep_periodic hq h, phaseRep_ae_line hq h,
    norm_phaseRep_le hq h⟩

/-- The continuous representative is unique ("canonical", tex 7387). -/
theorem phase_trace_unique (w : Yq P q) {g₁ g₂ : C(AddCircle P, Lp CVec3 q (volume : Measure Space))}
    (h₁ : (w : AddCircle P → Lp CVec3 q (volume : Measure Space)) =ᵐ[AddCircle.haarAddCircle] g₁)
    (h₂ : (w : AddCircle P → Lp CVec3 q (volume : Measure Space)) =ᵐ[AddCircle.haarAddCircle] g₂) :
    g₁ = g₂ := by
  have := (Continuous.ae_eq_iff_eq AddCircle.haarAddCircle g₁.continuous g₂.continuous).mp
    (h₁.symm.trans h₂)
  exact ContinuousMap.ext (congrFun this)

/-- **B0434 on the free graph** (INF25 `freeGraph_strongTrace`, constant `1`): every
`(w, νΔw, T₀w) ∈ D_(ν,q)` has a continuous phase representative with
`sup_τ ‖w(τ)‖ ≤ ‖w‖_{Y_q} + P ‖T₀w‖_{Y_q}`, uniformly in `ν` and `P`. -/
theorem freeGraph_strongTrace (hq : q ≠ ⊤) {ν : ℝ} {w a b : Yq P q}
    (hw : (w, a, b) ∈ freeGraph P ν q) :
    ∃ w' : C(AddCircle P, Lp CVec3 q (volume : Measure Space)),
      (w : AddCircle P → Lp CVec3 q (volume : Measure Space)) =ᵐ[AddCircle.haarAddCircle] w' ∧
        ∀ τ, ‖w' τ‖ ≤ ‖w‖ + P * ‖b‖ :=
  phase_trace hq hw.2

/-- **B0434 with the manuscript's constant** (`eq:free-stress-4`, tex 7393–7394):
`sup_τ ‖w(τ)‖_{L^q} ≤ (1 + 3P/(2q)) ‖w‖_{Y_q} + P ‖T₀w‖_{Y_q}`. -/
theorem freeGraph_strongTrace_manuscript (hq : q ≠ ⊤) {ν : ℝ} {w a b : Yq P q}
    (hw : (w, a, b) ∈ freeGraph P ν q) :
    ∃ w' : C(AddCircle P, Lp CVec3 q (volume : Measure Space)),
      (w : AddCircle P → Lp CVec3 q (volume : Measure Space)) =ᵐ[AddCircle.haarAddCircle] w' ∧
        ∀ τ, ‖w' τ‖ ≤ (1 + 3 * P / (2 * q.toReal)) * ‖w‖ + P * ‖b‖ := by
  obtain ⟨w', hae, hb⟩ := freeGraph_strongTrace hq hw
  refine ⟨w', hae, fun τ => (hb τ).trans ?_⟩
  have hP0 := hP.out
  have h1 : 0 ≤ 3 * P / (2 * q.toReal) := by positivity
  nlinarith [norm_nonneg w]

end UnforcedLeray.PhaseTrace
