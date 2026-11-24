import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_1_3
import Mathlib.Analysis.Calculus.FDeriv.Star

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem continuous_cjVec :
    Continuous fun v : CVec3 => (WithLp.toLp 2 fun i => (starRingEnd ℂ) (v i) : CVec3) := by
  fun_prop

theorem cjF_apply_norm (w : ℝ × Space → CVec3) (x : ℝ × Space) : ‖cjF w x‖ₑ = ‖w x‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
  congr 1
  simp [cjF, EuclideanSpace.norm_eq, Complex.norm_conj]

theorem phaseLpNorm_cjF (P : ℝ) (w : ℝ × Space → CVec3) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 (cjF w) = UnforcedLeray.Short.IIb.phaseLpNorm P 2 w := by
  unfold UnforcedLeray.Short.IIb.phaseLpNorm
  simp only [cjF_apply_norm]

theorem isInYr_cjF {P : ℝ} {w : ℝ × Space → CVec3} (hw : UnforcedLeray.Short.IIb.IsInYr P 2 w) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (cjF w) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hw.periodic] with x hx
    simp only [cjF]
    rw [hx]
  · exact (continuous_cjVec.comp_aestronglyMeasurable hw.meas)
  · rw [phaseLpNorm_cjF]
    exact hw.finite

theorem conj_phaseInt (P : ℝ) (f : ℝ × Space → ℂ) :
    phaseInt P (fun x => (starRingEnd ℂ) (f x)) = (starRingEnd ℂ) (phaseInt P f) := by
  simp [phaseInt, integral_conj, Complex.conj_ofReal]

theorem dy_conj (j : Fin 3) (φ : ℝ × Space → ℂ) (x : ℝ × Space) :
    UnforcedLeray.PhaseSpace.dy j (fun p => (starRingEnd ℂ) (φ p)) x
      = (starRingEnd ℂ) (UnforcedLeray.PhaseSpace.dy j φ x) := by
  have hs : (fun p => (starRingEnd ℂ) (φ p)) = fun p => star (φ p) := rfl
  unfold UnforcedLeray.PhaseSpace.dy
  rw [hs, fderiv_star]
  simp [starL', Complex.star_def]

theorem conj_gradT_eq (φ : ℝ × Space → ℂ) (x : ℝ × Space) :
    gradT (fun p => (starRingEnd ℂ) (φ p)) x = cjF (gradT φ) x := by
  ext i
  simp [UnforcedLeray.PhaseSpace.gradT, dy_conj, cjF, Pi.single_apply, map_sum, map_mul,
    apply_ite (starRingEnd ℂ), Finset.sum_apply]

theorem conj_pairF_gradT (P : ℝ) (φ : ℝ × Space → ℂ) (w : ℝ × Space → CVec3) :
    pairF P (gradT φ) (cjF w) = (starRingEnd ℂ) (pairF P (gradT (fun p => (starRingEnd ℂ) (φ p))) w) := by
  unfold pairF
  rw [← conj_phaseInt]
  congr 1
  funext x
  rw [conj_gradT_eq]
  simp [dotL_apply, cjF, Complex.conj_conj, map_sum, map_mul]

theorem isPhaseTest_conj {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) :
    IsPhaseTest P (fun p => (starRingEnd ℂ) (φ p)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).contDiff.comp hφ.smooth
  · intro τ y
    simp [hφ.periodic τ y]
  · obtain ⟨R, hR⟩ := hφ.bounded_support
    exact ⟨R, fun τ y h => by simp [hR τ y h]⟩

theorem fwuConj : FWUConj := by
  intro P w hw hs
  refine ⟨isInYr_cjF hw, ?_⟩
  intro φ hφ
  rw [conj_pairF_gradT]
  rw [hs _ (isPhaseTest_conj hφ)]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete
