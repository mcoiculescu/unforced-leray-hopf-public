import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WeakDmuAdd
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PairCont

/-!
# Subtracting two `Y_2` weak solutions (source 1580-1583, 1341-1344)

Proof of `WeakDmuSubY`.  The pairing of a phase test with a field of `Y_2` is additive in the
field slot (`pairF_add_right_of_integrable`), because a field of `Y_2` is `L²` on the phase cell
(`volume.restrict (phaseCell P) = muP P`) and a phase test pairs integrably with it
(`wda_integrable_dotL`).  Subtracting the two equations gives the homogeneous equation with
right side `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell
  pairF_add_right_of_integrable)

/-- The phase cell restriction of the volume is the phase measure `muP`. -/
theorem wds_restrict_cell_eq_muP (P : ℝ) :
    (volume : Measure (ℝ × Space)).restrict (phaseCell P) = muP P := by
  unfold phaseCell muP
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

/-- A `Y_2` field is `L²` for the phase measure. -/
theorem wds_memLp_muP {P : ℝ} (hP : 0 < P) {u : ℝ × Space → CVec3}
    (hu : UnforcedLeray.Short.IIb.IsInYr P 2 u) : MemLp u 2 (muP P) := by
  refine ⟨aesm_muP hu.meas, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (lint_lt_top_of_phaseLpNorm hP hu.meas hu.finite).ne

/-- A `Y_2` field is `L²` on the phase cell. -/
theorem wds_memLp_cell {P : ℝ} (hP : 0 < P) {u : ℝ × Space → CVec3}
    (hu : UnforcedLeray.Short.IIb.IsInYr P 2 u) :
    MemLp u 2 (volume.restrict (phaseCell P)) := by
  rw [wds_restrict_cell_eq_muP]
  exact wds_memLp_muP hP hu

/-- Additivity of the pairing of a phase test in the field slot, for `Y_2` fields. -/
theorem wds_pair_sub {P : ℝ} (hP : 0 < P) {H w w' : ℝ × Space → CVec3}
    (hH : IsPhaseTest P H) (hw : UnforcedLeray.Short.IIb.IsInYr P 2 w)
    (hw' : UnforcedLeray.Short.IIb.IsInYr P 2 w') :
    pairF P H (w - w') = pairF P H w - pairF P H w' := by
  have : Fact (0 < P) := ⟨hP⟩
  have hI : ∀ u : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 u →
      Integrable (fun x => dotL (H x) (u x)) (volume.restrict (phaseCell P)) :=
    fun u hu => wda_integrable_dotL hH.smooth.continuous hH.bounded_support
      (wds_memLp_cell hP hu)
  have hF : Integrable (fun x => dotL (H x) ((w - w') x)) (volume.restrict (phaseCell P)) :=
    ((hI w hw).sub (hI w' hw')).congr (Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, map_sub])
  have hFG : Integrable (fun x => dotL (H x) ((w - w') x + w' x))
      (volume.restrict (phaseCell P)) :=
    (hI w hw).congr (Eventually.of_forall fun x => by simp)
  have key := pairF_add_right_of_integrable (P := P) (H := H) (F := w - w') (G := w') hF
    (hI w' hw') hFG
  have hw_eq : (fun x => (w - w') x + w' x) = w := funext fun x => by simp
  rw [hw_eq] at key
  rw [key]
  ring

/-- **Subtracting two weak solutions** (source 1580-1583). -/
theorem weakDmuSubY : WeakDmuSubY := by
  intro ν μ P w w' rhs hP hw hw' h1 h2
  refine ⟨fun φ hφ => ?_, fun Φ hΦ => ?_⟩
  · rw [wds_pair_sub hP hφ.gradT hw hw', h1.solenoidal φ hφ, h2.solenoidal φ hφ, sub_zero]
  · have hT : IsPhaseTest P (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) :=
      (isPhaseTest_L0T hΦ.1 ν).add (hΦ.1.const_smul (μ : ℂ))
    rw [wds_pair_sub hP hT hw hw', h1.equation Φ hΦ, h2.equation Φ hΦ, sub_self]

end UnforcedLeray.Short.PartIIIb.Concrete
