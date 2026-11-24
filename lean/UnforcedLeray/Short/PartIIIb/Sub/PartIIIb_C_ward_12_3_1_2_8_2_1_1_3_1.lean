import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3.PiDecayOrder0
import UnforcedLeray.Lib.PhaseSpace.ExtendedTest

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1/3/1`: decomposition of `PiDecay`

Source `the November 2 reference manuscript`
lines 1393-1400, 1409-1412.  Order-zero decay is proved
(`PiDecayOrder0Aux.projPot_decay0_aux`).  For the derivatives, the far field is the Newton kernel
estimate `∂^α∂_iN(y-x) = O(|y|^{-2-|α|})` for `|y| ≥ 2R` (`Ψ` supported in `|x| ≤ R`), integrated
against `Ψ` (no cancellation is needed; `π = -∑_i ∫ ∂_iN(y-x)Ψ_i(x)dx`).  This is the Prop
`PiFarDeriv`; the reduction from it to `PiDecay` (continuity + periodicity + compactness on
`[0,P] × closedBall`) is proved here as `piDecay_of`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set Metric
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.PiDecayAssembly

open UnforcedLeray.PhaseSpace

/-- Far-field derivative bounds for `π = projPot Ψ`, uniform for `τ ∈ [0,P]`:
`∂π = O(|y|^{-3})`, `∂²π = O(|y|^{-4})`, `∂³π = O(|y|^{-5})` for `|y| ≥ ρ`
(source 1393-1400; kernel derivative `|∂^k∂N(z)| ≤ C|z|^{-2-k}` of
`Kernels.norm_iteratedFDeriv_newton_le`, `|y-x| ≥ |y|/2` on the support). -/
def PiFarDeriv : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Ψ : ℝ × UnforcedLeray.Space → CVec3), IsPhaseTest P Ψ →
    ∃ ρ C : ℝ, ∀ τ ∈ Icc (0 : ℝ) P, ∀ y : UnforcedLeray.Space, ρ ≤ ‖y‖ →
      (∀ j, ‖dy j (projPot Ψ) (τ, y)‖ ≤ C * ‖y‖ ^ (-3 : ℝ)) ∧
      (∀ j k, ‖dy j (dy k (projPot Ψ)) (τ, y)‖ ≤ C * ‖y‖ ^ (-4 : ℝ)) ∧
      ∀ i j k, ‖dy i (dy j (dy k (projPot Ψ))) (τ, y)‖ ≤ C * ‖y‖ ^ (-5 : ℝ)

theorem contDiff_dyC {f : ℝ × UnforcedLeray.Space → ℂ} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (dy j f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- Far-field decay + continuity + periodicity gives global decay. -/
theorem dec_of_far {P : ℝ} [Fact (0 < P)] {a : ℝ} (ha : a ≤ 0) {f : ℝ × UnforcedLeray.Space → ℂ}
    (hc : Continuous f) (hper : ∀ τ y, f (τ + P, y) = f (τ, y)) {ρ C : ℝ}
    (hfar : ∀ τ ∈ Icc (0 : ℝ) P, ∀ y : UnforcedLeray.Space, ρ ≤ ‖y‖ →
      ‖f (τ, y)‖ ≤ C * ‖y‖ ^ a) : Dec a f := by
  set T : ℝ := max ρ 1 with hT
  have hT1 : 1 ≤ T := le_max_right _ _
  have hTρ : ρ ≤ T := le_max_left _ _
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : UnforcedLeray.Space) T)).exists_bound_of_continuousOn
    hc.norm.continuousOn
  have hred : ∀ τ y, ∃ τ' ∈ Ico (0 : ℝ) P, f (τ', y) = f (τ, y) := by
    intro τ y
    have hp : Function.Periodic (fun t : ℝ => f (t, y)) P := fun t => hper t y
    obtain ⟨τ', hτ', h⟩ := hp.exists_mem_Ico₀ (Fact.out) τ
    exact ⟨τ', hτ', h.symm⟩
  have hpos : ∀ y : UnforcedLeray.Space, 0 < 1 + ‖y‖ := fun y => by positivity
  have h2a : (0 : ℝ) < 2 ^ (-a) := by positivity
  refine ⟨max M 0 * (1 + T) ^ (-a) + 2 ^ (-a) * max C 0, fun τ y => ?_⟩
  obtain ⟨τ', hτ', hEq⟩ := hred τ y
  have hQnn : 0 ≤ (1 + ‖y‖) ^ a := Real.rpow_nonneg (hpos y).le _
  have hmax0 : 0 ≤ max M 0 := le_max_right _ _
  have hTa : 0 ≤ (1 + T) ^ (-a) := Real.rpow_nonneg (by linarith) _
  rcases le_or_gt ‖y‖ T with hy | hy
  · have hm := hM (τ', y) ⟨⟨hτ'.1, hτ'.2.le⟩, mem_closedBall_zero_iff.mpr hy⟩
    rw [hEq] at hm
    have hm' : ‖f (τ, y)‖ ≤ M := by simpa using hm
    have h1 : (1 + T) ^ a ≤ (1 + ‖y‖) ^ a :=
      Real.rpow_le_rpow_of_nonpos (hpos y) (by linarith) ha
    have hone : 1 ≤ (1 + T) ^ (-a) * (1 + ‖y‖) ^ a := by
      have : (1 + T) ^ (-a) * (1 + T) ^ a = 1 := by
        rw [← Real.rpow_add (by linarith)]; simp
      calc (1 : ℝ) = (1 + T) ^ (-a) * (1 + T) ^ a := this.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 hTa
    have hnn : 0 ≤ 2 ^ (-a) * max C 0 * (1 + ‖y‖) ^ a := by
      have := le_max_right C 0
      positivity
    calc ‖f (τ, y)‖ ≤ M := hm'
      _ ≤ max M 0 := le_max_left _ _
      _ ≤ max M 0 * ((1 + T) ^ (-a) * (1 + ‖y‖) ^ a) := by
          nlinarith [mul_le_mul_of_nonneg_left hone hmax0]
      _ ≤ (max M 0 * (1 + T) ^ (-a) + 2 ^ (-a) * max C 0) * (1 + ‖y‖) ^ a := by
          nlinarith [hnn]
  · have hy1 : 1 ≤ ‖y‖ := by linarith
    have hyρ : ρ ≤ ‖y‖ := by linarith
    have h := hfar τ' ⟨hτ'.1, hτ'.2.le⟩ y hyρ
    rw [hEq] at h
    have hy0 : 0 < ‖y‖ := by linarith
    have hle : 2 * ‖y‖ ≥ 1 + ‖y‖ := by linarith
    have h3 : (2 * ‖y‖) ^ a ≤ (1 + ‖y‖) ^ a :=
      Real.rpow_le_rpow_of_nonpos (hpos y) hle ha
    rw [Real.mul_rpow (by norm_num) hy0.le] at h3
    have h4 : ‖y‖ ^ a ≤ 2 ^ (-a) * (1 + ‖y‖) ^ a := by
      have h2 : (2 : ℝ) ^ (-a) * 2 ^ a = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      calc ‖y‖ ^ a = 2 ^ (-a) * (2 ^ a * ‖y‖ ^ a) := by rw [← mul_assoc, h2, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 h2a.le
    have hyn : 0 ≤ ‖y‖ ^ a := Real.rpow_nonneg hy0.le _
    have hmC : C * ‖y‖ ^ a ≤ max C 0 * ‖y‖ ^ a :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hyn
    calc ‖f (τ, y)‖ ≤ C * ‖y‖ ^ a := h
      _ ≤ max C 0 * ‖y‖ ^ a := hmC
      _ ≤ max C 0 * (2 ^ (-a) * (1 + ‖y‖) ^ a) :=
          mul_le_mul_of_nonneg_left h4 (le_max_right _ _)
      _ ≤ (max M 0 * (1 + T) ^ (-a) + 2 ^ (-a) * max C 0) * (1 + ‖y‖) ^ a := by
          nlinarith [mul_nonneg hmax0 (mul_nonneg hTa hQnn)]

theorem piDecay_of (h : PiFarDeriv) : PiDecay := by
  intro P _ Ψ hΨ
  obtain ⟨ρ, C, hf⟩ := h P Ψ hΨ
  have hsm : ContDiff ℝ ∞ (projPot Ψ) := contDiff_projPot hΨ
  have hper : ∀ τ y, projPot Ψ (τ + P, y) = projPot Ψ (τ, y) :=
    fun τ y => PiDecayOrder0Aux.projPot_periodic_time hΨ y τ
  refine ⟨?_, fun j => ?_, fun j k => ?_, fun i j k => ?_⟩
  · exact PiDecayOrder0Aux.projPot_decay0_aux hΨ
  · exact dec_of_far (by norm_num) (contDiff_dyC hsm j).continuous (periodic_dy hper j)
      (fun τ hτ y hy => (hf τ hτ y hy).1 j)
  · exact dec_of_far (by norm_num) (contDiff_dyC (contDiff_dyC hsm k) j).continuous
      (periodic_dy (periodic_dy hper k) j) (fun τ hτ y hy => (hf τ hτ y hy).2.1 j k)
  · exact dec_of_far (by norm_num) (contDiff_dyC (contDiff_dyC (contDiff_dyC hsm k) j) i).continuous
      (periodic_dy (periodic_dy (periodic_dy hper k) j) i)
      (fun τ hτ y hy => (hf τ hτ y hy).2.2 i j k)

end UnforcedLeray.Short.PartIIIb.Concrete.PiDecayAssembly
