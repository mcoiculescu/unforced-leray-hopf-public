import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3
import UnforcedLeray.Short.PartIIa.Sub.F14_1
import UnforcedLeray.Short.PartIIa.Tasks.F13EnergyIdentity

/-!
# Part II-a, task `PartII-a:F09/3/2`: the adjoint Hilbert identity on `D_2`, from core density

Source `the November 2 reference manuscript`
lines 1424-1450 (the smooth core of `D_2`) and 1491-1496 (the energy identity).

`adjointEnergyD2_of` derives `AdjointEnergyD2` from `D2CoreDense` (task `PartII-a:F14/1/1`) and
the gradient-limit lemma `D2GradLimit`: for phase tests `G_n` with `G_n → w` and `νΔG_n → νΔw` in
`Y_2`, the gradients converge: `HasGrad w g` and `Σ_j ‖∂_j G_n‖² → Σ_j ‖g_j‖²`.
The identity on phase tests is `phaseTestSkew` and `phaseTestLap`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Gradient limit along a core sequence** (source 1446-1450, with `phaseTestLap`
`ν Σ_j ‖∂_j (G_n - G_m)‖² = Re ⟨-νΔ(G_n - G_m), G_n - G_m⟩ → 0`, so `∂_j G_n` is Cauchy in `Y_2`;
its limit is the gradient of `w` by `HasGrad` of `testElem (dy j G)` (integration by parts in the
slab, `B0005.integral_slab_dy`) and closedness of `HasPhaseOp`; uniqueness `hasGrad_unique`). -/
def D2GradLimit : Prop :=
  ∀ {P : ℝ} [Fact (0 < P)] {ν : ℝ}, 0 < ν → ∀ (w : D P ν 2) (G : ℕ → ℝ × Space → CVec3),
    (∀ n, IsPhaseTest P (G n)) →
    Tendsto (fun n => testElem P 2 (G n)) atTop (𝓝 (w : Yq P 2)) →
    Tendsto (fun n => testElem P 2 (nuLapT ν (G n))) atTop (𝓝 (nuLapD w)) →
    ∃ g : Fin 3 → Yq P 2, HasGrad (w : Yq P 2) g ∧
      Tendsto (fun n => ∑ j, ‖testElem P 2 (dy j (G n))‖ ^ 2) atTop (𝓝 (∑ j, ‖g j‖ ^ 2))

/-- The adjoint Hilbert identity on a phase test element:
`Re ⟨-T₀G - νΔG + G, G⟩ = ¼‖G‖² + ν Σ_j ‖∂_j G‖²`. -/
theorem adjointEnergy_testElem {P : ℝ} [Fact (0 < P)] (ν : ℝ) {G : ℝ × Space → CVec3}
    (hG : IsPhaseTest P G) :
    (inner ℂ (-(testElem P 2 (B0005.T0op G)) - testElem P 2 (nuLapT ν G) + testElem P 2 G)
        (testElem P 2 G)).re =
      1 / 4 * ‖testElem P 2 G‖ ^ 2 + ν * ∑ j, ‖testElem P 2 (dy j G)‖ ^ 2 := by
  have hG1 : IsPhaseTest P (B0005.T0op G) := B0005.IsPhaseTest.T0op hG
  have hG2 : IsPhaseTest P (nuLapT ν G) := hG.lapT.const_smul ν
  have hGj : ∀ j : Fin 3, IsPhaseTest P (dy j G) := fun j => hG.dy j
  set w := testElem P 2 G with hw
  have e : inner ℂ (-(testElem P 2 (B0005.T0op G)) - testElem P 2 (nuLapT ν G) + w) w =
      -inner ℂ (testElem P 2 (B0005.T0op G)) w - inner ℂ (testElem P 2 (nuLapT ν G)) w +
        inner ℂ w w := by
    rw [inner_add_left, inner_sub_left, inner_neg_left]
  have c1 : (inner ℂ (testElem P 2 (B0005.T0op G)) w).re = 3 / 4 * ‖w‖ ^ 2 := by
    rw [← inner_conj_symm, Complex.conj_re, inner_testElem_two hG hG1]
    rw [Complex.re_ofReal_mul, phaseTestSkew P G hG, hw, normSq_testElem hG]
    ring
  have c2 : (inner ℂ (testElem P 2 (nuLapT ν G)) w).re =
      -(ν * ∑ j, ‖testElem P 2 (dy j G)‖ ^ 2) := by
    rw [← inner_conj_symm, Complex.conj_re, inner_testElem_two hG hG2, phaseTestLap P ν G hG]
    have : (-(ν : ℂ) * ∑ j : Fin 3, slabInner P (dy j G) (dy j G)).re =
        -(ν * ∑ j : Fin 3, (slabInner P (dy j G) (dy j G)).re) := by
      rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul, Complex.re_sum]
    rw [Complex.re_ofReal_mul, this]
    have : ∀ j : Fin 3, ‖testElem P 2 (dy j G)‖ ^ 2 = P⁻¹ * (slabInner P (dy j G) (dy j G)).re :=
      fun j => normSq_testElem (hGj j)
    simp only [this, ← Finset.mul_sum]
    ring
  have c3 : (inner ℂ w w).re = ‖w‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [e]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, c1, c2, c3]
  ring

/-- **`AdjointEnergyD2` from core density and the gradient limit.** -/
theorem adjointEnergyD2_of (hcore : D2CoreDense) (hgl : D2GradLimit) : AdjointEnergyD2 := by
  intro P _ ν hν w
  obtain ⟨G, hG, hw, hT, hL⟩ := hcore P ν hν w
  obtain ⟨g, hg, hgl'⟩ := hgl hν w G hG hw hL
  refine ⟨g, hg, ?_⟩
  have hseq : ∀ n, (inner ℂ (-(testElem P 2 (B0005.T0op (G n))) - testElem P 2 (nuLapT ν (G n)) +
        testElem P 2 (G n)) (testElem P 2 (G n))).re =
      1 / 4 * ‖testElem P 2 (G n)‖ ^ 2 + ν * ∑ j, ‖testElem P 2 (dy j (G n))‖ ^ 2 :=
    fun n => adjointEnergy_testElem ν (hG n)
  have lim1 : Tendsto (fun n => (inner ℂ (-(testElem P 2 (B0005.T0op (G n))) -
        testElem P 2 (nuLapT ν (G n)) + testElem P 2 (G n)) (testElem P 2 (G n))).re) atTop
      (𝓝 (inner ℂ (-(T0D w) - nuLapD w + (w : Yq P 2)) (w : Yq P 2)).re) := by
    have h := Filter.Tendsto.inner (𝕜 := ℂ) (((hT.neg).sub hL).add hw) hw
    exact (Complex.continuous_re.tendsto _).comp h
  have lim2 : Tendsto (fun n => 1 / 4 * ‖testElem P 2 (G n)‖ ^ 2 +
      ν * ∑ j, ‖testElem P 2 (dy j (G n))‖ ^ 2) atTop
      (𝓝 (1 / 4 * ‖(w : Yq P 2)‖ ^ 2 + ν * ∑ j, ‖g j‖ ^ 2)) :=
    (((hw.norm).pow 2).const_mul _).add (hgl'.const_mul ν)
  exact tendsto_nhds_unique (lim1.congr hseq) lim2

end UnforcedLeray.Short.PartIIa
