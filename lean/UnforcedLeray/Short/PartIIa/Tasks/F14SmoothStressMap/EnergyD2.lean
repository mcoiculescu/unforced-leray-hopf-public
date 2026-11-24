import UnforcedLeray.Short.PartIIa.Sub.F14_1
import UnforcedLeray.Short.PartIIa.Tasks.F13EnergyIdentity
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.CoreDense
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.GradLimit
import UnforcedLeray.Units.B0005.Consistency
import UnforcedLeray.Units.B0411

/-!
# Part II-a, `PartII-a:F14/1/2`: the Hilbert energy identity on all of `D_2` (body operator)

Source of record: `the November 2 reference manuscript`, lines 1491-1496.

Proof shape (as in the accepted adjoint version `adjointEnergyD2_of`):
* `d2CoreDense` (task `PartII-a:F14/1/1`) gives phase tests `G n` with `G n → w`,
  `𝒯₀ G n → 𝒯₀ w`, `νΔ G n → νΔ w` in `Y_2`;
* `bodyEnergy_testElem` is the per-test identity from `freeEnergyIdentity` (lines 1491-1496);
* `d2GradLimit` (task `PartII-a:F09/3/2/1`) gives the gradient `g` with `HasGrad w g` and
  `Σ_j ‖∂_j G n‖² → Σ_j ‖g_j‖²`;
* the identity passes to the limit, and `inner` is swapped by `inner_conj_symm`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- The Hilbert identity on a phase test for the operator `μ + L₀`, with `L₀ G = 𝒯₀G - νΔG - ½G`
written on test elements. -/
theorem bodyEnergy_testElem {P : ℝ} [Fact (0 < P)] (ν : ℝ) (μ : ℂ) {G : ℝ × Space → CVec3}
    (hG : IsPhaseTest P G) :
    (inner ℂ (testElem P 2 G) (μ • testElem P 2 G + (testElem P 2 (B0005.T0op G) -
        testElem P 2 (nuLapT ν G) - (1 / 2 : ℂ) • testElem P 2 G))).re =
      (μ.re + 1 / 4) * ‖testElem P 2 G‖ ^ 2 + ν * ∑ j, ‖testElem P 2 (dy j G)‖ ^ 2 := by
  have hg : HasPhaseOp (L0T ν) (testElem P 2 G)
      (testElem P 2 (B0005.T0op G) - testElem P 2 (nuLapT ν G) - (1 / 2 : ℂ) • testElem P 2 G) :=
    hasPhaseOp_L0T (B0005.hasHLap_testElem hG ν) (B0005.hasT0_testElem hG)
  exact freeEnergyIdentity hG _ hg μ

/-- **`PartII-a:F14/1/2`: the energy identity on all of `D_2`.** -/
theorem smoothStressEnergyD2 : SmoothStressEnergyD2 := by
  intro P _ _ ν hν μ _ w
  obtain ⟨G, hG, hw, hT, hL⟩ := d2CoreDense P ν hν w
  obtain ⟨g, hg, hgl⟩ := d2GradLimit hν w G hG hw hL
  refine ⟨g, hg, ?_⟩
  have hseq : ∀ n, (inner ℂ (testElem P 2 (G n)) (μ • testElem P 2 (G n) +
        (testElem P 2 (B0005.T0op (G n)) - testElem P 2 (nuLapT ν (G n)) -
          (1 / 2 : ℂ) • testElem P 2 (G n)))).re =
      (μ.re + 1 / 4) * ‖testElem P 2 (G n)‖ ^ 2 +
        ν * ∑ j, ‖testElem P 2 (dy j (G n))‖ ^ 2 :=
    fun n => bodyEnergy_testElem ν μ (hG n)
  have hX : Tendsto (fun n => μ • testElem P 2 (G n) +
      (testElem P 2 (B0005.T0op (G n)) - testElem P 2 (nuLapT ν (G n)) -
        (1 / 2 : ℂ) • testElem P 2 (G n))) atTop
      (𝓝 (μ • (w : Yq P 2) + ((T0D w - nuLapD w) - (1 / 2 : ℂ) • (w : Yq P 2)))) :=
    (hw.const_smul μ).add ((hT.sub hL).sub (hw.const_smul (1 / 2 : ℂ)))
  have lim1 : Tendsto (fun n => (inner ℂ (testElem P 2 (G n)) (μ • testElem P 2 (G n) +
        (testElem P 2 (B0005.T0op (G n)) - testElem P 2 (nuLapT ν (G n)) -
          (1 / 2 : ℂ) • testElem P 2 (G n)))).re) atTop
      (𝓝 (inner ℂ (w : Yq P 2) (μ • (w : Yq P 2) + ((T0D w - nuLapD w) -
        (1 / 2 : ℂ) • (w : Yq P 2)))).re) :=
    (Complex.continuous_re.tendsto _).comp (Filter.Tendsto.inner (𝕜 := ℂ) hw hX)
  have lim2 : Tendsto (fun n => (μ.re + 1 / 4) * ‖testElem P 2 (G n)‖ ^ 2 +
      ν * ∑ j, ‖testElem P 2 (dy j (G n))‖ ^ 2) atTop
      (𝓝 ((μ.re + 1 / 4) * ‖(w : Yq P 2)‖ ^ 2 + ν * ∑ j, ‖g j‖ ^ 2)) :=
    (((hw.norm).pow 2).const_mul _).add (hgl.const_mul ν)
  have key := tendsto_nhds_unique (lim1.congr hseq) lim2
  have hb : bodyOp P ν 2 μ w = μ • (w : Yq P 2) + ((T0D w - nuLapD w) -
      (1 / 2 : ℂ) • (w : Yq P 2)) := rfl
  rw [hb, ← inner_conj_symm, Complex.conj_re]
  exact key

end UnforcedLeray.Short.PartIIa
