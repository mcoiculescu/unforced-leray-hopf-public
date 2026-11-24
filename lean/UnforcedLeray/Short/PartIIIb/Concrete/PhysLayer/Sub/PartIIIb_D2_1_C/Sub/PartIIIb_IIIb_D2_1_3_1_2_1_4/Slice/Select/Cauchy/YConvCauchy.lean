import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PhaseLpTri2

/-!
# `cYConvCauchy`: convergence in `Y_2` implies Cauchy (source 1341-1344)

Triangle inequality `phaseLpNorm_tri_aux` for `(Ψₙ - Φ) + (Φ - Ψₘ)`, with the sign swap
`phaseLpNorm (Φ - Ψₘ) = phaseLpNorm (Ψₘ - Φ)` (`enorm_neg`), and `ε/2 + ε/2 = ε`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem cyC_norm_sub_comm (P : ℝ) (a b : ℝ × Space → CVec3) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => a x - b x)
      = UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => b x - a x) := by
  have h : (fun x => b x - a x) = fun x => -(a x - b x) := funext fun x => (neg_sub (a x) (b x)).symm
  rw [h]
  unfold UnforcedLeray.Short.IIb.phaseLpNorm
  simp only [enorm_neg]

theorem cYConvCauchy : CYConvCauchy := by
  intro P hP Ψ Φ hΨ hΦ hconv
  unfold YCauchy
  intro ε hε
  have hη : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  have hev : ∀ᶠ n in atTop,
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => Ψ n x - Φ x) < ε / 2 :=
    Filter.Tendsto.eventually hconv (gt_mem_nhds hη)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n m hn hm => ?_⟩
  have htri := phaseLpNorm_tri_aux P (Ψ n) Φ (Ψ m) (hΨ n).meas hΦ.meas (hΨ m).meas
  rw [cyC_norm_sub_comm P Φ (Ψ m)] at htri
  have h1 := hN n hn
  have h2 := hN m hm
  calc _ ≤ _ := htri
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add h1 h2
    _ = ε := ENNReal.add_halves ε

end UnforcedLeray.Short.PartIIIb.Concrete
