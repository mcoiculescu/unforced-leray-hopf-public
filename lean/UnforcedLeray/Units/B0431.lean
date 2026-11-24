import UnforcedLeray.Units.B0428

/-!
# Unit B0431 (`eq:free-stress-6`): viscosity-weighted gradient bound in the graph

Blueprint unit `B0431`, label `eq:free-stress-6`, `paper/main.tex` lines 7402–7406 (the
theorem of §`sec:st18-8879`, source range 7268–8686); proof at tex 7682–7683. Dependency:
B0428 (`eq:free-stress-19`, tex 7541–7548, drafted in `Units/B0428.lean`). Consumer noted in
the blueprint: tex 3658 (`eq:free-background-b-3`, at `q = 11/4`).

**Statement (tex 7402–7406).** `‖∇w‖_{Y_q} ≤ C_q ν^{-1/2} ‖w‖_{D_(ν,q)}`, stated for `q > 5/2`,
and "the latter gradient estimate also holds for every `1 < q < ∞`" (tex 7405–7406). Standing
hypotheses (tex 7306–7308): `ν > 0`, `0 < P ≤ 1`; `C_q` is independent of `P` and `ν`
(tex 7385). The graph and its norm are `eq:free-stress-1` (tex 7322–7327):
`D_(ν,q) = {w ∈ Y_q : νΔw ∈ Y_q, T₀w ∈ Y_q}`,
`‖w‖_{D_(ν,q)} = ‖w‖_{Y_q} + ‖νΔw‖_{Y_q} + ‖T₀w‖_{Y_q}`.

**Formalization.**
* `Y_q` is `PhaseSpace.Yq P q` with its normalised norm, `D_(ν,q)` is `B0411.D P ν q` and the
  graph norm is `B0411.graphNormD` (unit B0411, decision D2 of

* `∂ⱼw = g` is `HasPhaseOp (fun Φ => -dy j Φ) w g`, the convention of B0428; the gradient is
  the triple `g : Fin 3 → Y_q`, whose norm is the maximum of the component norms. Since the
  derivatives are unique (`B0428.phaseDeriv_unique`), the bounds are stated for *every* such
  triple (`norm_grad_graph_le`), and existence is `exists_grad_graph`. The sum of the component
  norms (which dominates any pointwise matrix norm of `∇w` up to a fixed factor) is bounded
  with the extra factor `3`.
* The constant is `gradConstD = gradConst / 2` (`gradConst` of B0428), independent of `P`, `q`
  and `ν` (the manuscript allows dependence on `q`).
* `B0431_spec`: the whole unit, with `ν^{-1/2}` written as the real power `ν ^ (-(1/2))` of
  `ν > 0` (no junk value: the base is positive).

**Proof (tex 7682–7683, blueprint outline).** "Formula (19), integrated in normalized phase
measure, proves (6)": B0428's graph form `B0428.exists_phaseDeriv_graph` already is the
integrated statement `‖∂ⱼw‖_{Y_q} ≤ C ν^{-1/2} ‖w‖_{Y_q}^{1/2} ‖νΔw‖_{Y_q}^{1/2}` (using
`‖Δw‖^{1/2} = ν^{-1/2}‖νΔw‖^{1/2}`), and AM–GM `√a √b ≤ (a + b)/2 ≤ ‖w‖_{D_(ν,q)}/2` finishes.

Hypotheses: exactly the manuscript's or weaker (`1 < q < ∞`, `ν > 0`, `P > 0`; `P ≤ 1` is not
needed). No junk values: the only power is of `ν > 0`, the square roots are of nonnegative
reals, and there is no division by a norm.

Status: the unit is proved in full relative to the compiled drafts it imports (B0428, B0411).
Theorem A is not proved in Lean.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.B0431

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
open UnforcedLeray.Heat UnforcedLeray.PhaseSpace

/-- The constant of `eq:free-stress-6` (tex 7403–7404): `gradConst / 2`, with `gradConst` the
interpolation constant of B0428 (`eq:free-stress-19`). Independent of `P`, `q` and `ν`. -/
def gradConstD : ℝ := B0428.gradConst / 2

theorem gradConstD_nonneg : 0 ≤ gradConstD := by
  have := B0428.gradConst_nonneg
  unfold gradConstD
  positivity

/-- AM–GM in the form used at tex 7682–7683: `√a √b ≤ (a + b)/2` for `a, b ≥ 0`. -/
theorem sqrt_mul_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ (a + b) / 2 := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b)]

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

/-- **B0431, one component** (`eq:free-stress-6`, tex 7402–7406, all `1 < q < ∞`): for `ν > 0`,
`w ∈ D_(ν,q)` and any `g ∈ Y_q` with `∂ⱼw = g` in distributions,
`‖g‖_{Y_q} ≤ C ν^{-1/2} ‖w‖_{D_(ν,q)}`. -/
theorem norm_phaseDeriv_graph_le (hq1 : 1 < q) (hqt : q ≠ ⊤) {ν : ℝ} (hν : 0 < ν)
    (w : B0411.D P ν q) {j : Fin 3} {g : Yq P q}
    (hg : HasPhaseOp (fun Φ => -dy j Φ) (w : Yq P q) g) :
    ‖g‖ ≤ gradConstD * (Real.sqrt ν)⁻¹ * B0411.graphNormD w := by
  obtain ⟨g', hg', hn⟩ := B0428.exists_phaseDeriv_graph hq1 hqt hν w j
  rw [B0428.phaseDeriv_unique hg hg']
  refine hn.trans ?_
  have hAM := sqrt_mul_sqrt_le (norm_nonneg (w : Yq P q)) (norm_nonneg (B0411.nuLapD w))
  have hT := norm_nonneg (B0411.T0D w)
  have hC := B0428.gradConst_nonneg
  have hs : 0 ≤ (Real.sqrt ν)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  unfold B0411.graphNormD gradConstD
  calc B0428.gradConst * (Real.sqrt ν)⁻¹ *
        (Real.sqrt ‖(w : Yq P q)‖ * Real.sqrt ‖B0411.nuLapD w‖)
      ≤ B0428.gradConst * (Real.sqrt ν)⁻¹ *
        ((‖(w : Yq P q)‖ + ‖B0411.nuLapD w‖ + ‖B0411.T0D w‖) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC hs)
    _ = B0428.gradConst / 2 * (Real.sqrt ν)⁻¹ *
        (‖(w : Yq P q)‖ + ‖B0411.nuLapD w‖ + ‖B0411.T0D w‖) := by ring

/-- **B0431, the gradient** (`eq:free-stress-6`, tex 7402–7406, all `1 < q < ∞`): for `ν > 0`,
`w ∈ D_(ν,q)` and any triple `g` with `∂ⱼw = gⱼ` in distributions,
`‖∇w‖_{Y_q} = maxⱼ ‖gⱼ‖_{Y_q} ≤ C ν^{-1/2} ‖w‖_{D_(ν,q)}` and
`∑ⱼ ‖gⱼ‖_{Y_q} ≤ 3C ν^{-1/2} ‖w‖_{D_(ν,q)}`. -/
theorem norm_grad_graph_le (hq1 : 1 < q) (hqt : q ≠ ⊤) {ν : ℝ} (hν : 0 < ν)
    (w : B0411.D P ν q) {g : Fin 3 → Yq P q}
    (hg : ∀ j, HasPhaseOp (fun Φ => -dy j Φ) (w : Yq P q) (g j)) :
    ‖g‖ ≤ gradConstD * (Real.sqrt ν)⁻¹ * B0411.graphNormD w ∧
      ∑ j, ‖g j‖ ≤ 3 * (gradConstD * (Real.sqrt ν)⁻¹ * B0411.graphNormD w) := by
  have hj : ∀ j, ‖g j‖ ≤ gradConstD * (Real.sqrt ν)⁻¹ * B0411.graphNormD w :=
    fun j => norm_phaseDeriv_graph_le hq1 hqt hν w (hg j)
  refine ⟨(pi_norm_le_iff_of_nonneg ((norm_nonneg (g 0)).trans (hj 0))).2 hj, ?_⟩
  calc ∑ j, ‖g j‖ ≤ ∑ _j : Fin 3, gradConstD * (Real.sqrt ν)⁻¹ * B0411.graphNormD w :=
        Finset.sum_le_sum fun j _ => hj j
    _ = 3 * (gradConstD * (Real.sqrt ν)⁻¹ * B0411.graphNormD w) := by simp

/-- **B0431 with existence** (tex 7402–7406, all `1 < q < ∞`): every `w ∈ D_(ν,q)`, `ν > 0`,
has a distributional gradient `∇w ∈ Y_q³` (B0428), it is unique, and
`‖∇w‖_{Y_q} ≤ C ν^{-1/2} ‖w‖_{D_(ν,q)}`. -/
theorem exists_grad_graph (hq1 : 1 < q) (hqt : q ≠ ⊤) {ν : ℝ} (hν : 0 < ν)
    (w : B0411.D P ν q) :
    ∃ g : Fin 3 → Yq P q, (∀ j, HasPhaseOp (fun Φ => -dy j Φ) (w : Yq P q) (g j)) ∧
      (∀ g' : Fin 3 → Yq P q,
        (∀ j, HasPhaseOp (fun Φ => -dy j Φ) (w : Yq P q) (g' j)) → g' = g) ∧
      ‖g‖ ≤ gradConstD * (Real.sqrt ν)⁻¹ * B0411.graphNormD w ∧
      ∑ j, ‖g j‖ ≤ 3 * (gradConstD * (Real.sqrt ν)⁻¹ * B0411.graphNormD w) := by
  have hL := B0428.hasPhaseOp_lapT_of_nuLapT hν.ne' (B0411.hasPhaseOp_nuLapD w)
  obtain ⟨g, hg, -, -⟩ := B0428.exists_phaseGrad hq1 hqt hL
  exact ⟨g, hg, fun g' hg' => funext fun j => B0428.phaseDeriv_unique (hg' j) (hg j),
    norm_grad_graph_le hq1 hqt hν w hg⟩

/-- `ν^{-1/2}` as a real power equals `(√ν)⁻¹` for `ν > 0`. -/
theorem rpow_neg_half_eq {ν : ℝ} (hν : 0 < ν) : ν ^ (-(1 / 2 : ℝ)) = (Real.sqrt ν)⁻¹ := by
  rw [Real.rpow_neg hν.le, Real.sqrt_eq_rpow]

/-- **Unit B0431** (`eq:free-stress-6`, tex 7402–7406, for every `1 < q < ∞`, tex 7405–7406):
there is `C ≥ 0`, independent of `P`, `q` and `ν`, such that for `P > 0`, `ν > 0` and every
`w ∈ D_(ν,q)` the distributional gradient `∇w` exists in `Y_q³`, is unique, and
`‖∇w‖_{Y_q} ≤ C ν^{-1/2} ‖w‖_{D_(ν,q)}`. -/
theorem B0431_spec :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ →
      ∀ ν : ℝ, 0 < ν → ∀ w : B0411.D P ν q,
        ∃ g : Fin 3 → Yq P q, (∀ j, HasPhaseOp (fun Φ => -dy j Φ) (w : Yq P q) (g j)) ∧
          (∀ g' : Fin 3 → Yq P q,
            (∀ j, HasPhaseOp (fun Φ => -dy j Φ) (w : Yq P q) (g' j)) → g' = g) ∧
          ‖g‖ ≤ C * ν ^ (-(1 / 2 : ℝ)) * B0411.graphNormD w := by
  refine ⟨gradConstD, gradConstD_nonneg, fun P _ q _ hq1 hqt ν hν w => ?_⟩
  obtain ⟨g, hg, hu, hn, -⟩ := exists_grad_graph hq1 hqt hν w
  exact ⟨g, hg, hu, by rw [rpow_neg_half_eq hν]; exact hn⟩

end UnforcedLeray.B0431
