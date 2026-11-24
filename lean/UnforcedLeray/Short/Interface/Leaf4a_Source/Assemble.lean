import UnforcedLeray.Short.Interface.WindowSteps2
import UnforcedLeray.Units.B0423

/-!
# Interface leaf 4a, conditional assembly of the window estimate (task `Interface:I17`)

`sourceWindowRegularity_of` takes the four window steps as hypotheses, exactly as
`l3BackgroundOfPath_of` and `periodicModeEquationToLine_of` do for the other interface leaves:

* `WindowChartEquationLocal` (step W1a, task `Interface:I12`, `eq:free-stress-13`);
* `WindowChartTimeChange` (step W1b, task `Interface:I13`, `eq:free-stress-14`);
* `WindowChartL2` (step W2, task `Interface:I14`);
* `WindowTransportBack` (step W4, task `Interface:I15`).

The heat maximal regularity is the compiled `UnforcedLeray.B0423.heat_estimate_laplacian`
(`Units/B0423.lean`, `q = 2`, `d = 3`). The unconditional `sourceWindowRegularity` in
`Short/Interface/Leaf4a_Source.lean` applies this theorem to the four named theorems.

The cutoff of step W1 (`paper/main.tex` line 7490) is `ContDiffBump 0` with `rIn = 1`,
`rOut = 3/2`, so its support is `closedBall 0 (3/2) ⊆ Ioo (-2) 2` and it equals `1` on `[-1,1]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08 UnforcedLeray.Parabolic

/-- The bump function with `rIn = 1` and `rOut = 3/2`. -/
private def windowBump : ContDiffBump (0 : ℝ) :=
  { rIn := 1, rOut := 3 / 2, rIn_pos := one_pos, rIn_lt_rOut := by norm_num }

/-- A window cutoff exists (`χ ∈ C_c^∞(-2,2)`, `χ = 1` on `[-1,1]`, line 7490). -/
theorem exists_isWindowCutoff : ∃ χ : ℝ → ℝ, IsWindowCutoff χ := by
  refine ⟨⇑windowBump, ?_, ?_, ?_, ?_⟩
  · exact windowBump.contDiff
  · exact windowBump.hasCompactSupport
  · intro x hx
    rw [windowBump.tsupport_eq, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
      abs_le] at hx
    have hr : windowBump.rOut = 3 / 2 := rfl
    rw [hr] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro t ht
    apply windowBump.one_of_mem_closedBall
    have hr : windowBump.rIn = 1 := rfl
    rw [hr, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
    exact ⟨ht.1, ht.2⟩

/-- The window estimate `SourceWindowRegularity`, conditional on the four window steps. The
proof takes the cutoff, applies `(W1a)` and `(W1b)` to get the heat equation for `u_i`, `(W2)`
for the `L²` membership, the compiled heat maximal regularity with `ν = h`, `q = 2`, `d = 3` for
the weak second derivatives, and `(W4)` for the conclusion. -/
theorem sourceWindowRegularity_of
    (hA : WindowChartEquationLocal) (hB : WindowChartTimeChange) (hC : WindowChartL2)
    (hD : WindowTransportBack) : SourceWindowRegularity := by
  intro h μ P w f hh hP hw hf hsol τ₀
  obtain ⟨χ, hχ⟩ := exists_isWindowCutoff
  refine hD P w χ τ₀ hP hw hχ ?_
  intro i
  have hEq := hA h μ P w f τ₀ i hh hP hw hf hsol
  have hHeat := hB h μ P w f χ τ₀ i hh hP hw hf hχ hEq
  obtain ⟨hu, hF⟩ := hC h μ P w f χ τ₀ i hP hw hf hχ
  have hu' : MemLp (windowU χ τ₀ w i) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact hu
  have hF' : MemLp (windowF χ μ τ₀ w f i) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact hF
  obtain ⟨_, hH⟩ := UnforcedLeray.B0423.heat_estimate_laplacian (d := 3)
    (by norm_num : (1 : ℝ) < 2)
  obtain ⟨D2, _, hD2, _⟩ := hH h hh (windowU χ τ₀ w i) (windowF χ μ τ₀ w f i) hu' hF' hHeat
  refine ⟨D2, fun a b => ⟨?_, (hD2 a b).2⟩⟩
  have h2 := (hD2 a b).1
  rw [ENNReal.ofReal_ofNat] at h2
  exact h2

end UnforcedLeray.Short.Interface
