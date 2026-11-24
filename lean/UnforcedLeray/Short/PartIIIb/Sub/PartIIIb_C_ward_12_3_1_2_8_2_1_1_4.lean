import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.ProjCommuteProps
import UnforcedLeray.Short.PartIIb.Tasks.OrdRelUnique.TestElemLimit
import NavierStokes.R3.ComparisonCutoffs

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1/4`: `GradPairingGeneral` via the cutoff limit

Source `the November 2 reference manuscript`
lines 1393-1400, 1409-1412.  Assembly: `⟪∇(χ_{n+1}σ), v⟫ = 0` (`IsPhaseSolenoidal`, as
`χ_{n+1}σ` is a phase test), `∇(χ_{n+1}σ) → ∇σ` in `L^{q₀'}` slices uniformly
(`GPCutoffLimit`), and `PhasePairLimit` (from the proved `testElemLimit`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology MeasureTheory Set
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace

/-- The cutoff product `χ_{n+1} σ` (`χ_R = NavierStokesR3.ComparisonCutoffs.cutoff R`,
equal to `1` on `|y| ≤ R`, `0` for `|y| ≥ 2R`). -/
def cutoffMul (σ : ℝ × UnforcedLeray.Space → ℂ) (n : ℕ) : ℝ × UnforcedLeray.Space → ℂ :=
  fun z => ((NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1) z.2 : ℝ) : ℂ) * σ z

theorem isPhaseTest_cutoffMul {P : ℝ} {σ : ℝ × UnforcedLeray.Space → ℂ} (hs : ContDiff ℝ ∞ σ)
    (hp : ∀ τ y, σ (τ + P, y) = σ (τ, y)) (n : ℕ) : IsPhaseTest P (cutoffMul σ n) where
  smooth := by
    unfold cutoffMul
    refine ((Complex.ofRealCLM.contDiff.comp
      ((NavierStokesR3.ComparisonCutoffs.cutoff_smooth ((n : ℝ) + 1)).comp contDiff_snd))).mul hs
  periodic := by
    intro τ y
    simp [cutoffMul, hp τ y]
  bounded_support := by
    refine ⟨2 * ((n : ℝ) + 1), fun τ y hy => ?_⟩
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have := NavierStokesR3.ComparisonCutoffs.cutoff_eq_zero hR (x := y) (by linarith)
    simp [cutoffMul, this]

/-- The hypotheses of `GradPairingGeneral` on `σ`. -/
def SigmaHyp (P : ℝ) (σ : ℝ × UnforcedLeray.Space → ℂ) : Prop :=
  ContDiff ℝ ∞ σ ∧ (∀ τ y, σ (τ + P, y) = σ (τ, y)) ∧
    ∃ C : ℝ, ∀ τ y, ‖σ (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) ∧
      ‖gradT σ (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-3 : ℝ)

/-- **Lemma A (slice test).**  Under `SigmaHyp`, `∇σ` is `P`-periodic (it is, as `σ` is) and
slice-continuous into `L^{q₀'}`: `|∇σ| ≤ C(1+|y|)^{-3}` and `(1+|y|)^{-33/7}` is integrable on `ℝ³`
(`33/7 > 3`), so `∇σ(τ,·) ∈ L^{11/7}`; continuity in `τ` by dominated convergence
(`∇σ` continuous, dominating function independent of `τ`). -/
def GPSlice : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (σ : ℝ × UnforcedLeray.Space → ℂ), SigmaHyp P σ →
    IsSliceTest P (conjExp UnforcedLeray.B0412.q0E) (gradT σ)

/-- **Lemma B (cutoff limit, uniformly in the phase).**  With
`∇(χ_{n+1}σ) = χ_{n+1}∇σ + σ∇χ_{n+1}`: the `L^{11/7}` slice distance to `∇σ` tends to `0` for each
`τ ∈ [0,P]` (tail of `|y|^{-33/7}` for `(1-χ)∇σ`; `|σ∇χ_R| ≤ C R^{-1}(1+|y|)^{-2}` on the shell
`R ≤ |y| ≤ 2R`, of volume `O(R³)`, so norm `O(R^{-3+21/11}) → 0`) and is bounded uniformly in
`n` and `τ ∈ [0,P]`. -/
def GPCutoffLimit : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (σ : ℝ × UnforcedLeray.Space → ℂ), SigmaHyp P σ →
    (∀ τ ∈ Icc (0 : ℝ) P, Tendsto (fun n : ℕ =>
      eLpNorm (fun y => gradT (cutoffMul σ n) (τ, y) - gradT σ (τ, y))
        (conjExp UnforcedLeray.B0412.q0E) volume) atTop (𝓝 0)) ∧
    ∃ C : ℝ, ∀ (n : ℕ), ∀ τ ∈ Icc (0 : ℝ) P,
      eLpNorm (fun y => gradT (cutoffMul σ n) (τ, y) - gradT σ (τ, y))
        (conjExp UnforcedLeray.B0412.q0E) volume ≤ ENNReal.ofReal C

theorem gradPairingGeneral_of (hA : GPSlice) (hB : GPCutoffLimit) : GradPairingGeneral := by
  intro P _ σ hs hp hdec
  have hyp : SigmaHyp P σ := ⟨hs, hp, hdec⟩
  have hsl := hA P σ hyp
  refine ⟨hsl, fun v hv => ?_⟩
  obtain ⟨hlim, hbd⟩ := hB P σ hyp
  have hΘ : ∀ n, IsSliceTest P (conjExp UnforcedLeray.B0412.q0E) (gradT (cutoffMul σ n)) :=
    fun n => (isPhaseTest_cutoffMul hs hp n).gradT.isSliceTest _
  have hT := UnforcedLeray.Short.IIb.phasePairLimit_of UnforcedLeray.Short.IIb.testElemLimit
    P (fun n => gradT (cutoffMul σ n)) (gradT σ) hΘ hsl hlim hbd v
  have h0 : ∀ n, phasePair P UnforcedLeray.B0412.q0E (gradT (cutoffMul σ n)) v = 0 :=
    fun n => hv _ (isPhaseTest_cutoffMul hs hp n)
  simp only [h0] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

end UnforcedLeray.Short.PartIIIb.Concrete
