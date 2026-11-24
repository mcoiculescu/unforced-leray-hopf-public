import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncMemY

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace AdjRemMemAux

theorem fin_smul_aux {P : ℝ} (hP : 0 < P) (c : ℂ) {f : ℝ × Space → CVec3}
    (hf : AEStronglyMeasurable f volume)
    (hfin : UnforcedLeray.Short.IIb.phaseLpNorm P 2 f < ⊤) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => c • f x) < ⊤ :=
  phaseLpNorm_lt_top_of_enorm_le hP (K := ‖c‖ₑ) enorm_ne_top (hf.const_smul c) hf hfin
    (fun x => le_of_eq (enorm_smul c _))

theorem fin_add_aux {P : ℝ} (hP : 0 < P) {u v : ℝ × Space → CVec3}
    (hu : AEStronglyMeasurable u volume) (hv : AEStronglyMeasurable v volume)
    (hfu : UnforcedLeray.Short.IIb.phaseLpNorm P 2 u < ⊤)
    (hfv : UnforcedLeray.Short.IIb.phaseLpNorm P 2 v < ⊤) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => u x + v x) < ⊤ :=
  lt_of_le_of_lt (phaseLpNorm_add_le P hP u v hu hv) (ENNReal.add_lt_top.2 ⟨hfu, hfv⟩)

end AdjRemMemAux

open AdjRemMemAux in
theorem adjRemainderMem : AdjRemainderMem := by
  intro P ν μ hP _ _ _ Φ g a b hdom ha hb
  have hR : remH μ Φ g a b
      = fun x => ((((1 + μ : ℝ) : ℂ) • Φ x + (-1 : ℂ) • a x) + (-1 : ℂ) • b x) + (-1 : ℂ) • g x := by
    funext x
    simp only [remH, neg_one_smul, sub_eq_add_neg]
  have m1 : AEStronglyMeasurable (((1 + μ : ℝ) : ℂ) • Φ) volume :=
    hdom.mem.meas.const_smul _
  have m2 : AEStronglyMeasurable ((-1 : ℂ) • a) volume := ha.meas.const_smul _
  have m3 : AEStronglyMeasurable ((-1 : ℂ) • b) volume := hb.meas.const_smul _
  have m4 : AEStronglyMeasurable ((-1 : ℂ) • g) volume := hdom.mem_g.meas.const_smul _
  have f1 := fin_smul_aux hP (((1 + μ : ℝ) : ℂ)) hdom.mem.meas hdom.mem.finite
  have f2 := fin_smul_aux hP (-1 : ℂ) ha.meas ha.finite
  have f3 := fin_smul_aux hP (-1 : ℂ) hb.meas hb.finite
  have f4 := fin_smul_aux hP (-1 : ℂ) hdom.mem_g.meas hdom.mem_g.finite
  have s1 := fin_add_aux hP m1 m2 f1 f2
  have s2 := fin_add_aux hP (u := fun x => ((1 + μ : ℝ) : ℂ) • Φ x + (-1 : ℂ) • a x)
    (v := fun x => (-1 : ℂ) • b x) (m1.add m2) m3 s1 f3
  have s3 := fin_add_aux hP (u := fun x => ((1 + μ : ℝ) : ℂ) • Φ x + (-1 : ℂ) • a x
    + (-1 : ℂ) • b x) (v := fun x => (-1 : ℂ) • g x) ((m1.add m2).add m3) m4 s2 f4
  rw [hR]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hdom.mem.periodic, ha.periodic, hb.periodic, hdom.mem_g.periodic]
      with x h1 h2 h3 h4
    simp only [h1, h2, h3, h4]
  · exact (((m1.add m2).add m3).add m4)
  · exact s3

end UnforcedLeray.Short.PartIIIb.Concrete
