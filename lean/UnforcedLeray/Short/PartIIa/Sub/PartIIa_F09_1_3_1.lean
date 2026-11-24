import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1_3

/-!
# Part II-a, audit decomposition of `PartII-a:F09/1/3/1` (`adjPhaseTaylor`)

Source `the November 2 reference manuscript` lines 1403-1413, 1426-1428.
The representative of `x ↦ ⟪Φ, S(s)^* x⟫` is `ψ_s = 𝒯(s) Φ` (forward phase-translated free action
on the test, in `Y_{2'}`), by Hilbert duality (`PhaseDualityAdjT`). Its Taylor expansion is
reduced to the slicewise statement `SliceFwdTaylor`, lifted to `Y_{2'}` by `Lp.norm_le_of_ae_bound`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Hilbert duality of the phase semigroup on a test** (lines 1403-1413): for `s ≥ 0` and a phase
test `Φ`, `⟪Φ, S(s)^* x⟫ = ⟪𝒯(s)Φ, x⟫` where `𝒯(s)` is `B0421.phaseT` on `Y_{2'}`
(`phaseT` commutes with complex conjugation, `B0421.cx`/`freeC`, so the Hermitian adjoint turns
into the bilinear pairing). -/
def PhaseDualityAdjT : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
    ∀ s : ℝ, 0 ≤ s → ∀ x : Yq P 2,
      phasePair P 2 Φ (adjT P ν s x) =
        phasePairing P 2 (B0421.phaseT (P := P) (q := conjExp 2)
          (conjExp_ne_top (by norm_num)) ν s (testElem P (conjExp 2) Φ)) x

/-- **Slicewise forward Taylor bound** (lines 1403-1413, `d/ds 𝒯(s)Φ|₀ = -L₀Φ`): for a phase test
`Φ`, `ν > 0`, `1 ≤ p < ∞`, uniformly in the phase `t` and `0 < s ≤ 1`,
`‖S_ν(s) Φ(t - s,·) - Φ(t,·) + s (L₀Φ)(t,·)‖_{L^p} ≤ C s²`. -/
def SliceFwdTaylor : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν →
    ∀ Φ : ℝ × Space → CVec3, ∀ hΦ : IsPhaseTest P Φ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t s : ℝ, 0 < s → s ≤ 1 →
        ‖B0421.freeC hp ν s (sliceMap (hΦ.isSliceTest p).2 (t - s)) -
            sliceMap (hΦ.isSliceTest p).2 t +
            (s : ℂ) • sliceMap ((isPhaseTest_L0' hΦ ν).isSliceTest p).2 t‖ ≤ C * s ^ 2

set_option maxHeartbeats 1600000 in
/-- **`AdjPhaseTaylor` from the slicewise Taylor bound and the duality.** -/
theorem adjPhaseTaylor_of (h1 : SliceFwdTaylor) (h3 : PhaseDualityAdjT) : AdjPhaseTaylor := by
  intro P _ ν hν Φ hΦ
  have hp : conjExp 2 ≠ ⊤ := conjExp_ne_top (by norm_num)
  obtain ⟨C, hC0, hT⟩ := h1 (conjExp 2) hp P ν hν Φ hΦ
  refine ⟨C, hC0, fun s hs0 hs1 => ?_⟩
  have hs : IsSliceTest P (conjExp 2) Φ := hΦ.isSliceTest (conjExp 2)
  have hL : IsPhaseTest P (L0 ν Φ) := isPhaseTest_L0' hΦ ν
  have hsL : IsSliceTest P (conjExp 2) (L0 ν Φ) := hL.isSliceTest (conjExp 2)
  refine ⟨B0421.phaseT (P := P) (q := conjExp 2) hp ν s (testElem P (conjExp 2) Φ),
    fun x => h3 P ν hν Φ hΦ s hs0.le x, ?_⟩
  have hψ0 : ⇑(testElem P (conjExp 2) Φ) =ᵐ[AddCircle.haarAddCircle] ⇑(circleSlice hs) := by
    rw [testElem_of hs]
    exact ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp 2) (volume : Measure Space))
      (p := conjExp 2) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs)
  have hgT : ⇑(testElem P (conjExp 2) (L0 ν Φ)) =ᵐ[AddCircle.haarAddCircle]
      ⇑(circleSlice hsL) := by
    rw [testElem_of hsL]
    exact ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp 2) (volume : Measure Space))
      (p := conjExp 2) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hsL)
  have hψs := B0421.coeFn_phaseT (P := P) (q := conjExp 2) hp ν s (testElem P (conjExp 2) Φ)
  have hshift : ∀ᵐ τ ∂(AddCircle.haarAddCircle : Measure (AddCircle P)),
      (testElem P (conjExp 2) Φ) (τ - (s : AddCircle P)) = circleSlice hs (τ - (s : AddCircle P)) := by
    have := (measurePreserving_sub_right (AddCircle.haarAddCircle : Measure (AddCircle P))
      (s : AddCircle P)).quasiMeasurePreserving.ae_eq_comp hψ0
    exact this
  have hpt : ∀ τ : AddCircle P,
      ‖B0421.freeC hp ν s (circleSlice hs (τ - (s : AddCircle P))) - circleSlice hs τ +
        (s : ℂ) • circleSlice hsL τ‖ ≤ C * s ^ 2 := by
    intro τ
    induction τ using QuotientAddGroup.induction_on with
    | H t =>
      have e : ((t : AddCircle P) - (s : AddCircle P)) = ((t - s : ℝ) : AddCircle P) := by
        push_cast; rfl
      rw [e]
      simp only [circleSlice_coe]
      exact hT t s hs0 hs1
  have hfC : ∀ᵐ τ ∂(AddCircle.haarAddCircle : Measure (AddCircle P)),
      ‖(B0421.phaseT (P := P) (q := conjExp 2) hp ν s (testElem P (conjExp 2) Φ) -
        testElem P (conjExp 2) Φ + (s : ℂ) • testElem P (conjExp 2) (L0 ν Φ)) τ‖
        ≤ C * s ^ 2 := by
    filter_upwards [Lp.coeFn_add
        (B0421.phaseT (P := P) (q := conjExp 2) hp ν s (testElem P (conjExp 2) Φ) -
          testElem P (conjExp 2) Φ) ((s : ℂ) • testElem P (conjExp 2) (L0 ν Φ)),
      Lp.coeFn_sub (B0421.phaseT (P := P) (q := conjExp 2) hp ν s (testElem P (conjExp 2) Φ))
        (testElem P (conjExp 2) Φ),
      Lp.coeFn_smul (s : ℂ) (testElem P (conjExp 2) (L0 ν Φ)),
      hψs, hψ0, hgT, hshift] with τ e1 e2 e3 e4 e5 e6 e7
    simp only [e1, e2, e3, e4, e5, e6, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, e7]
    exact hpt τ
  have hbd := Lp.norm_le_of_ae_bound (μ := (AddCircle.haarAddCircle : Measure (AddCircle P)))
    (C := C * s ^ 2) (mul_nonneg hC0 (sq_nonneg s)) hfC
  have hmu : measureUnivNNReal (AddCircle.haarAddCircle (T := P)) = 1 := by
    simp [measureUnivNNReal]
  simpa [hmu] using hbd

end UnforcedLeray.Short.PartIIa
