import UnforcedLeray.Units.B0224.FiberHeat
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.FibreBasicAux

theorem reduceIoc_add_any (c q : ℝ) :
    UnforcedLeray.B0220.reduceIoc c (q + c) = UnforcedLeray.B0220.reduceIoc c q := by
  by_cases hc : c = 0
  · subst hc
    simp [UnforcedLeray.B0220.reduceIoc]
  · have hdiv : (q + c) / c = q / c + 1 := by field_simp
    unfold UnforcedLeray.B0220.reduceIoc
    rw [hdiv, Int.ceil_add_one]
    push_cast
    ring

end UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.FibreBasicAux

theorem heatFibreBasic_holds (c : ℝ) :
    UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.HeatFibreBasic c := by
  intro g s
  constructor
  · exact (UnforcedLeray.B0224.stronglyMeasurable_periodize (Lp.stronglyMeasurable g)).comp_measurable
      (measurable_const.prodMk measurable_id)
  · intro z
    simp only [UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.fibre, UnforcedLeray.B0220.periodize,
      UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.FibreBasicAux.reduceIoc_add_any]
