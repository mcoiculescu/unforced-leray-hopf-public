import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2
import UnforcedLeray.Units.B0224.FiberHeat

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0220 (HSpace Profile measureH periodize)
open UnforcedLeray.B0224 (strip heatTime measurable_heatTime fiberHeat stronglyMeasurable_fiberHeat
  stronglyMeasurable_periodize)
open UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong

theorem heatAgeMeas_holds (c : ℝ) : UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.HeatAgeMeas c := by
  intro ν t g
  have hG : StronglyMeasurable (g : Profile → MeridC) := Lp.stronglyMeasurable g
  have hP : StronglyMeasurable (periodize c (g : Profile → MeridC)) := stronglyMeasurable_periodize hG
  have hF : StronglyMeasurable (fiberHeat c (heatTime ν t) (g : Profile → MeridC)) :=
    stronglyMeasurable_fiberHeat (measurable_heatTime ν t) hG
  constructor
  · have hm : Measurable (fun p : Profile =>
        ‖fiberHeat c (heatTime ν t) (g : Profile → MeridC) p - periodize c (g : Profile → MeridC) p‖ₑ ^ 2) :=
      ((hF.sub hP).measurable.enorm).pow_const 2
    exact hm.lintegral_prod_right' (ν := volume.restrict (strip c))
  · have hm : Measurable (fun p : Profile => ‖periodize c (g : Profile → MeridC) p‖ₑ ^ 2) :=
      (hP.measurable.enorm).pow_const 2
    exact hm.lintegral_prod_right' (ν := volume.restrict (strip c))
