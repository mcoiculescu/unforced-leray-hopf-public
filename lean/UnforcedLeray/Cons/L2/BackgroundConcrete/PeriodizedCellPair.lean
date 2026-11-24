import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF
import UnforcedLeray.Lib.PhaseTrace.Periodize

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.PhaseTrace
open UnforcedLeray.B0412

/-- A compact phase-time supported function has no translated copies on the reference cell. -/
theorem perT_eq_self_on_Ioc {P A B : ℝ} (hP : 0 < P) (hA : 0 < A) (hB : B < P)
    {G : ℝ × Space → ℂ} (hG : TimeSupp A B G) {τ : ℝ}
    (hτ : τ ∈ Ioc 0 P) (y : Space) :
    perT P G (τ, y) = G (τ, y) := by
  have hs : ∀ k : ℤ, (τ, y).1 + k * P ∈ Icc A B → k ∈ ({0} : Finset ℤ) := by
    intro k hk
    have hk0 : k = 0 := by
      by_contra hk0
      have hkcases : k ≤ -1 ∨ 1 ≤ k := by omega
      rcases hkcases with hkn | hkp
      · have hkn' : (k : ℝ) ≤ -1 := by exact_mod_cast hkn
        have hshift : τ + (k : ℝ) * P ≤ τ - P := by
          nlinarith [mul_le_mul_of_nonneg_right hkn' hP.le]
        have hupper : τ - P ≤ 0 := by linarith [hτ.2]
        have := hk.1
        change A ≤ τ + (k : ℝ) * P at this
        linarith
      · have hkp' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkp
        have hshift : P < τ + (k : ℝ) * P := by
          nlinarith [mul_le_mul_of_nonneg_right hkp' hP.le, hτ.1]
        have := hk.2
        change τ + (k : ℝ) * P ≤ B at this
        linarith
    simp [hk0]
  rw [perT_eq_sum hG ({0} : Finset ℤ) (τ, y) hs]
  simp

/-- On the open phase cell, spatial derivatives of the periodization equal those of the
interior-supported function. The open-cell guard is needed because the endpoint `τ=P` is a seam. -/
theorem gradT_perT_eq_self_on_Ioo {P A B : ℝ} (hP : 0 < P) (hA : 0 < A) (hB : B < P)
    {G : ℝ × Space → ℂ} (hG : TimeSupp A B G) {τ : ℝ}
    (hτ0 : 0 < τ) (hτP : τ < P) (y : Space) :
    PhaseSpace.gradT (perT P G) (τ, y) = PhaseSpace.gradT G (τ, y) := by
  have hnhds : {z : ℝ × Space | z.1 ∈ Ioo 0 P} ∈ 𝓝 (τ, y) := by
    exact (continuous_fst.isOpen_preimage _ isOpen_Ioo).mem_nhds ⟨hτ0, hτP⟩
  have heq : perT P G =ᶠ[𝓝 (τ, y)] G := by
    filter_upwards [hnhds] with z hz
    exact perT_eq_self_on_Ioc hP hA hB hG ⟨hz.1, hz.2.le⟩ z.2
  unfold PhaseSpace.gradT
  simp only [PhaseSpace.dy]
  congr 1
  funext j
  rw [heq.fderiv_eq]

/-- Phase solenoidality annihilates every compactly phase-supported smooth scalar test after
periodization, with the exact normalized period integral representative. -/
theorem phaseSolenoidal_pairF_grad_perT_zero {P : ℝ} [Fact (0 < P)]
    {w : Yq P q0E} (hw : IsPhaseSolenoidal w)
    {G : ℝ × Space → ℂ} {A B : ℝ} (hG : TimeSupp A B G)
    (hG0 : IsPhaseTest 0 G) :
    pairF P (PhaseSpace.gradT (perT P G)) (fun x => rep w x.1 x.2) = 0 := by
  let htest : IsPhaseTest P (perT P G) := isPhaseTest_perT Fact.out hG hG0
  have hzero := hw (perT P G) htest
  rw [phasePair_eq_pairF_rep htest.gradT w] at hzero
  exact hzero

#print axioms perT_eq_self_on_Ioc
#print axioms gradT_perT_eq_self_on_Ioo
#print axioms phaseSolenoidal_pairF_grad_perT_zero

end UnforcedLeray.Cons.C03.Concrete
