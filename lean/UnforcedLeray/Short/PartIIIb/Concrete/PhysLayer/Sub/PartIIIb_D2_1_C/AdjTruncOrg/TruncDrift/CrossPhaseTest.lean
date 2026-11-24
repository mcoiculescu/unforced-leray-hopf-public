import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_12

/-!
# `CrossPhaseTest`: `∇c × Θ` and `c Θ` are phase tests (source 1351-1362, 1470-1480)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- Real scalar multiple of a phase test by a smooth, periodic multiplier. -/
theorem cpt_smul_real {P : ℝ} {m : ℝ × Space → ℝ} (hm : ContDiff ℝ ∞ m)
    (hmp : ∀ τ y, m (τ + P, y) = m (τ, y)) {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    IsPhaseTest P (fun q => m q • Θ q) where
  smooth := hm.smul hΘ.smooth
  periodic := fun τ y => by simp only [hmp, hΘ.periodic]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΘ.bounded_support
    exact ⟨R, fun τ y h => by simp [hR τ y h]⟩

/-- The map `v ↦ a × v` is smooth in the phase variable. -/
theorem cpt_crossC_contDiff {a : CVec3} {Θ : ℝ × Space → CVec3} (hΘ : ContDiff ℝ ∞ Θ) :
    ContDiff ℝ ∞ (fun q => crossC a (Θ q)) := by
  refine (contDiff_piLp 2).2 fun i => ?_
  have h0 : ContDiff ℝ ∞ (fun q : ℝ × Space => Θ q 0) :=
    (EuclideanSpace.proj (0 : Fin 3) : CVec3 →L[ℂ] ℂ).restrictScalars ℝ |>.contDiff.comp hΘ
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × Space => Θ q 1) :=
    (EuclideanSpace.proj (1 : Fin 3) : CVec3 →L[ℂ] ℂ).restrictScalars ℝ |>.contDiff.comp hΘ
  have h2 : ContDiff ℝ ∞ (fun q : ℝ × Space => Θ q 2) :=
    (EuclideanSpace.proj (2 : Fin 3) : CVec3 →L[ℂ] ℂ).restrictScalars ℝ |>.contDiff.comp hΘ
  fin_cases i
  · simp only [crossC]
    simp
    exact (contDiff_const.mul h2).sub (contDiff_const.mul h1)
  · simp only [crossC]
    simp
    exact (contDiff_const.mul h0).sub (contDiff_const.mul h2)
  · simp only [crossC]
    simp
    exact (contDiff_const.mul h1).sub (contDiff_const.mul h0)

/-- `v ↦ a × v` applied to a phase test is a phase test. -/
theorem cpt_crossC_phase {P : ℝ} (a : CVec3) {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    IsPhaseTest P (fun q => crossC a (Θ q)) where
  smooth := cpt_crossC_contDiff hΘ.smooth
  periodic := fun τ y => by simp only [hΘ.periodic]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΘ.bounded_support
    exact ⟨R, fun τ y h => by simp [hR τ y h, crossC]⟩

/-- Decomposition of `∇c × b` along the coordinate vectors. -/
theorem cpt_crossC_gradC (c : Space → ℝ) (y : Space) (b : CVec3) :
    crossC (gradC c y) b = ∑ j : Fin 3, (sd j c y) • crossC (EuclideanSpace.single j (1 : ℂ)) b := by
  ext i
  fin_cases i <;> simp [crossC, gradC, Fin.sum_univ_three] <;> ring

theorem crossPhaseTest : CrossPhaseTest := by
  intro P c hc Θ hΘ
  constructor
  · have hsum : (fun q : ℝ × Space => crossC (gradC c q.2) (Θ q))
        = ∑ j : Fin 3, (fun q : ℝ × Space => (sd j c q.2) • crossC (EuclideanSpace.single j (1 : ℂ)) (Θ q)) := by
      funext q
      rw [cpt_crossC_gradC c q.2 (Θ q), Finset.sum_apply]
    rw [hsum]
    refine IsPhaseTest.sum _ fun j _ => ?_
    exact cpt_smul_real ((contDiff_sd hc j).comp contDiff_snd) (fun τ y => rfl)
      (cpt_crossC_phase _ hΘ)
  · exact cpt_smul_real (hc.comp contDiff_snd) (fun τ y => rfl) hΘ

end UnforcedLeray.Short.PartIIIb.Concrete
