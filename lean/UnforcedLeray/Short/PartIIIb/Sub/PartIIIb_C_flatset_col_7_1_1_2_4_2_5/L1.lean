import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_5

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem measRep_ex : MeasRepP := by
  intro c hc f'
  have hm : AEStronglyMeasurable
      (fun p : UnforcedLeray.B0220.Profile => (UnforcedLeray.Short.PartIIa.PepsC 0 c f' :
        UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p)
      (UnforcedLeray.B0220.measureH c) := Lp.aestronglyMeasurable _
  refine ⟨fun p => ((p.1 : ℝ) : ℂ)⁻¹ • hm.mk _ p, ?_, ?_⟩
  · exact (Measurable.inv (Complex.measurable_ofReal.comp measurable_fst)).smul
      hm.stronglyMeasurable_mk.measurable
  · filter_upwards [hm.ae_eq_mk] with p hp
    rw [sfcGp, hp]
