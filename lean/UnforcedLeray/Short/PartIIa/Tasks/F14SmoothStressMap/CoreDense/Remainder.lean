import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.Defs
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.CoreDense.FwdRegular
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.CoreDense.FwdDecay
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.CoreDense.FwdSliceL2
import UnforcedLeray.Short.PartIIa.Tasks.F05bSliceContOfDecay

/-!
# Part II-a, task `PartII-a:F14/1/1/6`: the remainder tends to zero in `Y_2`

Target: `FwdRemainderBound` (defined in `Sub/F14_1_org/Defs.lean`).

Source of record: `the November 2 reference manuscript`, line 1463 with the rate of
line 1376.

Proof. Let `G = fwdIntegrand ν μ f M`.
* `IsSliceTest P 2 G`: periodicity from `fwdIntegrandRegular`, slice continuity from
  `sliceContOfDecay` (`q = 2`, `s = 2`) with the decay bound of `fwdIntegrandDecay` at `t = M`.
* Norm: pointwise on the phase circle, `‖circleSlice G x‖ₑ ≤ e^{-aM} ‖circleSlice f (x - M)‖ₑ`
  by `fwdSliceL2`; then the `Y_2` norms are the `L²(haarAddCircle)` integrals
  (`lintegral_enorm_rpow_Yq`), and the Haar measure is translation invariant.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace

/-- The `L²` norm of a slice map is the `eLpNorm` of the slice. -/
theorem fwdSliceMap_enorm {r : ℝ≥0∞} [Fact (1 ≤ r)] {Φ : ℝ × Space → CVec3}
    (h : SliceCont r Φ) (τ : ℝ) :
    ‖sliceMap h τ‖ₑ = eLpNorm (fun y => Φ (τ, y)) r volume := by
  unfold sliceMap
  rw [Lp.enorm_def]
  exact eLpNorm_congr_ae (MemLp.coeFn_toLp _)

/-- The `Y_2` norm is the translation-invariant integral of the slice norms. -/
theorem fwd_lintegral_circleSlice {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3}
    (hΦ : IsSliceTest P 2 Φ) :
    ∫⁻ x, ‖circleSlice hΦ x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂AddCircle.haarAddCircle
      = ‖testElem P 2 Φ‖ₑ ^ (2 : ℝ≥0∞).toReal := by
  have hq2 : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  rw [← lintegral_enorm_rpow_Yq (testElem P 2 Φ) hq2]
  apply lintegral_congr_ae
  rw [testElem_of hΦ]
  filter_upwards [ContinuousMap.coeFn_toLp (E := Lp CVec3 2 (volume : Measure Space))
    (p := 2) (𝕜 := ℂ) (μ := AddCircle.haarAddCircle) (circleSlice hΦ)] with x hx
  rw [hx]

/-- **The remainder tends to zero in `Y_2`** (line 1463, with the rate of line 1376). -/
theorem fwdRemainderBound : FwdRemainderBound := by
  intro P _hPfact ν hν μ f hf M hM
  have hP : 0 < P := _hPfact.out
  obtain ⟨hFs, hFp, -, -⟩ := fwdIntegrandRegular P ν hP hν μ f hf
  obtain ⟨C, hC0, hCb⟩ := fwdIntegrandDecay P ν hP hν μ f hf M 2
  -- the remainder is a slice test
  have hG : IsSliceTest P 2 (fwdIntegrand ν μ f M) := by
    refine ⟨fun τ y => hFp M τ y, ?_⟩
    have hs : (3 : ℝ) < ((2 : ℕ) : ℝ) * (2 : ℝ≥0∞).toReal := by norm_num
    have hq : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
    exact sliceContOfDecay 2 hq _ C hs _ (hFs M).continuous fun τ y =>
      (hCb M ⟨hM, le_rfl⟩ τ y).1
  have hf' : IsSliceTest P 2 f := (hf.isPhaseSchwartz 2).sliceTest
  set c : ℝ := Real.exp (-(μ.re + 1 / 4) * M) with hcdef
  have hc0 : (0 : ℝ) ≤ c := (Real.exp_pos _).le
  have hp0 : (0 : ℝ) ≤ (2 : ℝ≥0∞).toReal := ENNReal.toReal_nonneg
  have hp0' : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  -- pointwise bound on the phase circle
  have hpt : ∀ x : AddCircle P, ‖circleSlice hG x‖ₑ ≤
      ENNReal.ofReal c * ‖circleSlice hf' (x - (M : AddCircle P))‖ₑ := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      have e : (t : AddCircle P) - (M : AddCircle P) = ((t - M : ℝ) : AddCircle P) :=
        rfl
      rw [e, circleSlice_coe, circleSlice_coe, fwdSliceMap_enorm, fwdSliceMap_enorm]
      exact fwdSliceL2 P ν hP hν μ f hf M t hM
  -- translation invariance of the Haar measure
  have htr : ∫⁻ x, ‖circleSlice hf' (x - (M : AddCircle P))‖ₑ ^ (2 : ℝ≥0∞).toReal
      ∂AddCircle.haarAddCircle = ∫⁻ x, ‖circleSlice hf' x‖ₑ ^ (2 : ℝ≥0∞).toReal
      ∂AddCircle.haarAddCircle :=
    lintegral_sub_right_eq_self (fun y => ‖circleSlice hf' y‖ₑ ^ (2 : ℝ≥0∞).toReal) _
  have hcne : ENNReal.ofReal c ^ (2 : ℝ≥0∞).toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp0 ENNReal.ofReal_ne_top
  have key : ‖testElem P 2 (fwdIntegrand ν μ f M)‖ₑ ^ (2 : ℝ≥0∞).toReal
      ≤ (ENNReal.ofReal c) ^ (2 : ℝ≥0∞).toReal * ‖testElem P 2 f‖ₑ ^ (2 : ℝ≥0∞).toReal := by
    calc ‖testElem P 2 (fwdIntegrand ν μ f M)‖ₑ ^ (2 : ℝ≥0∞).toReal
        = ∫⁻ x, ‖circleSlice hG x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂AddCircle.haarAddCircle :=
          (fwd_lintegral_circleSlice hG).symm
      _ ≤ ∫⁻ x, (ENNReal.ofReal c * ‖circleSlice hf' (x - (M : AddCircle P))‖ₑ)
            ^ (2 : ℝ≥0∞).toReal ∂AddCircle.haarAddCircle :=
          lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hp0
      _ = ∫⁻ x, ENNReal.ofReal c ^ (2 : ℝ≥0∞).toReal
            * ‖circleSlice hf' (x - (M : AddCircle P))‖ₑ ^ (2 : ℝ≥0∞).toReal
            ∂AddCircle.haarAddCircle :=
          lintegral_congr fun x => ENNReal.mul_rpow_of_nonneg _ _ hp0
      _ = ENNReal.ofReal c ^ (2 : ℝ≥0∞).toReal
            * ∫⁻ x, ‖circleSlice hf' (x - (M : AddCircle P))‖ₑ ^ (2 : ℝ≥0∞).toReal
            ∂AddCircle.haarAddCircle :=
          lintegral_const_mul' _ _ hcne
      _ = ENNReal.ofReal c ^ (2 : ℝ≥0∞).toReal
            * ∫⁻ x, ‖circleSlice hf' x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂AddCircle.haarAddCircle := by
          rw [htr]
      _ = ENNReal.ofReal c ^ (2 : ℝ≥0∞).toReal * ‖testElem P 2 f‖ₑ ^ (2 : ℝ≥0∞).toReal := by
          rw [fwd_lintegral_circleSlice hf']
  have hle : ‖testElem P 2 (fwdIntegrand ν μ f M)‖ₑ
      ≤ ENNReal.ofReal c * ‖testElem P 2 f‖ₑ :=
    (ENNReal.rpow_le_rpow_iff hp0').1 (by rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]; exact key)
  have hfin := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0] at hfin
  exact ⟨hG, hfin⟩

end UnforcedLeray.Short.PartIIa
