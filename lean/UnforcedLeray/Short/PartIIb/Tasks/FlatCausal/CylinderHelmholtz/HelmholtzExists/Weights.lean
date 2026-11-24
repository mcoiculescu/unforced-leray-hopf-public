import UnforcedLeray.Short.PartIIb.Sub.T12
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzExists.Bounded
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzExists.Pair

/-!
# Weights of cylinder tests

For a cylinder test `φ` (`CylTest c φ`) the two weights `z ↦ ∂_q φ z`, `z ↦ ∂_η φ z` are
continuous, `c`-periodic, bounded and vanish for `|η|` large. The same holds for the components
of a solenoidal test field `Ψ` (`CylSolTest c Ψ`). These give the hypotheses of `cylPair_tendsto`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem fderiv_apply_add_period {c : ℝ} {φ : ℝ × ℝ → ℝ}
    (hper : ∀ z : ℝ × ℝ, φ (z.1 + c, z.2) = φ z) (z v : ℝ × ℝ) :
    fderiv ℝ φ (z.1 + c, z.2) v = fderiv ℝ φ z v := by
  have hfun : (fun y : ℝ × ℝ => φ (y + (c, 0))) = φ := by
    funext y
    have e : y + (c, 0) = (y.1 + c, y.2) := by
      ext <;> simp
    rw [e]
    exact hper y
  have h1 : fderiv ℝ (fun y : ℝ × ℝ => φ (y + (c, 0))) z = fderiv ℝ φ (z + (c, 0)) :=
    fderiv_comp_add_right (c, 0)
  rw [hfun] at h1
  have h2 : (z.1 + c, z.2) = z + (c, 0) := by
    ext <;> simp
  rw [h2, h1]

theorem fderiv_eq_zero_of_far {L : ℝ} {φ : ℝ × ℝ → ℝ}
    (hL : ∀ z : ℝ × ℝ, L < |z.2| → φ z = 0) (z : ℝ × ℝ) (hz : L < |z.2|) (v : ℝ × ℝ) :
    fderiv ℝ φ z v = 0 := by
  have hopen : IsOpen {y : ℝ × ℝ | L < |y.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  have hev : φ =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    exact hL y hy
  rw [hev.fderiv_eq]
  simp

theorem cylTest_fderiv_continuous {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (v : ℝ × ℝ) :
    Continuous (fun z => fderiv ℝ φ z v) :=
  (hφ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem cylTest_fderiv_bound {c : ℝ} (hc : 0 < c) {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ)
    (v : ℝ × ℝ) : ∃ M : ℝ, ∀ z : ℝ × ℝ, ‖(fderiv ℝ φ z v : ℂ)‖ ≤ M := by
  obtain ⟨L, hL⟩ := hφ.bounded
  obtain ⟨M, hM⟩ := bounded_of_periodic hc (f := fun z => fderiv ℝ φ z v)
    (cylTest_fderiv_continuous hφ.smooth v)
    (fun z => fderiv_apply_add_period hφ.periodic z v)
    (fun z hz => fderiv_eq_zero_of_far hL z hz v)
  refine ⟨M, fun z => ?_⟩
  rw [Complex.norm_real]
  exact hM z

/-- The two weights of a cylinder test, as a `Fin 2`-indexed family. -/
def testWeights (φ : ℝ × ℝ → ℝ) : Fin 2 → ℝ × ℝ → ℂ :=
  ![fun z => (fderiv ℝ φ z (1, 0) : ℂ), fun z => (fderiv ℝ φ z (0, 1) : ℂ)]

theorem cylTest_weights {c : ℝ} (hc : 0 < c) {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) :
    (∀ i : Fin 2, Continuous (testWeights φ i)) ∧
    (∃ M : ℝ, ∀ i : Fin 2, ∀ z : ℝ × ℝ, ‖testWeights φ i z‖ ≤ M) ∧
    (∃ L : ℝ, ∀ i : Fin 2, ∀ z : ℝ × ℝ, L < |z.2| → testWeights φ i z = 0) := by
  obtain ⟨L, hL⟩ := hφ.bounded
  obtain ⟨M1, hM1⟩ := cylTest_fderiv_bound hc hφ (1, 0)
  obtain ⟨M2, hM2⟩ := cylTest_fderiv_bound hc hφ (0, 1)
  refine ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, ⟨max M1 M2, Fin.forall_fin_two.2 ⟨fun z => ?_, fun z => ?_⟩⟩,
    ⟨L, Fin.forall_fin_two.2 ⟨fun z hz => ?_, fun z hz => ?_⟩⟩⟩
  · exact Complex.continuous_ofReal.comp (cylTest_fderiv_continuous hφ.smooth (1, 0))
  · exact Complex.continuous_ofReal.comp (cylTest_fderiv_continuous hφ.smooth (0, 1))
  · show ‖(fderiv ℝ φ z (1, 0) : ℂ)‖ ≤ max M1 M2
    exact (hM1 z).trans (le_max_left _ _)
  · show ‖(fderiv ℝ φ z (0, 1) : ℂ)‖ ≤ max M1 M2
    exact (hM2 z).trans (le_max_right _ _)
  · show ((fderiv ℝ φ z (1, 0) : ℝ) : ℂ) = 0
    rw [fderiv_eq_zero_of_far hL z hz (1, 0)]
    simp
  · show ((fderiv ℝ φ z (0, 1) : ℝ) : ℂ) = 0
    rw [fderiv_eq_zero_of_far hL z hz (0, 1)]
    simp

theorem cylSol_weights {c : ℝ} (hc : 0 < c) {Ψ : ℝ × ℝ → Fin 2 → ℝ} (hΨ : CylSolTest c Ψ) :
    (∀ i : Fin 2, Continuous (fun z => (Ψ z i : ℂ))) ∧
    (∃ M : ℝ, ∀ i : Fin 2, ∀ z : ℝ × ℝ, ‖(Ψ z i : ℂ)‖ ≤ M) ∧
    (∃ L : ℝ, ∀ i : Fin 2, ∀ z : ℝ × ℝ, L < |z.2| → (Ψ z i : ℂ) = 0) := by
  obtain ⟨L0, hL0⟩ := (hΨ.comp 0).bounded
  obtain ⟨L1, hL1⟩ := (hΨ.comp 1).bounded
  have hc0 := (hΨ.comp 0)
  have hc1 := (hΨ.comp 1)
  have hcont0 : Continuous (fun z => Ψ z 0) := (hΨ.comp 0).smooth.continuous
  have hcont1 : Continuous (fun z => Ψ z 1) := (hΨ.comp 1).smooth.continuous
  obtain ⟨M0, hM0⟩ := bounded_of_periodic hc (f := fun z => Ψ z 0) hcont0
    (fun z => (hΨ.comp 0).periodic z) (fun z hz => hL0 z hz)
  obtain ⟨M1, hM1⟩ := bounded_of_periodic hc (f := fun z => Ψ z 1) hcont1
    (fun z => (hΨ.comp 1).periodic z) (fun z hz => hL1 z hz)
  refine ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, ⟨max M0 M1, Fin.forall_fin_two.2 ⟨fun z => ?_, fun z => ?_⟩⟩,
    ⟨max L0 L1, Fin.forall_fin_two.2 ⟨fun z hz => ?_, fun z hz => ?_⟩⟩⟩
  · exact Complex.continuous_ofReal.comp hcont0
  · exact Complex.continuous_ofReal.comp hcont1
  · show ‖((Ψ z 0 : ℝ) : ℂ)‖ ≤ max M0 M1
    rw [Complex.norm_real]
    exact (hM0 z).trans (le_max_left _ _)
  · show ‖((Ψ z 1 : ℝ) : ℂ)‖ ≤ max M0 M1
    rw [Complex.norm_real]
    exact (hM1 z).trans (le_max_right _ _)
  · show ((Ψ z 0 : ℝ) : ℂ) = 0
    rw [hL0 z (lt_of_le_of_lt (le_max_left _ _) hz)]
    simp
  · show ((Ψ z 1 : ℝ) : ℂ) = 0
    rw [hL1 z (lt_of_le_of_lt (le_max_right _ _) hz)]
    simp

end UnforcedLeray.Short.IIb
