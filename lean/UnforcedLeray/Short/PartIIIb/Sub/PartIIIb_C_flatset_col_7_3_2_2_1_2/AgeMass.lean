import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2
import UnforcedLeray.Units.B0224.FiberHeat

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0220 (HSpace Profile measureH cellMeasure weightH measurable_weightH measurableSet_cell)
open UnforcedLeray.B0224 (strip cellMeasure_eq_prod' periodize_slice_of_mem measurableSet_strip)
open UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong

theorem heatAgeMass_holds (c : ℝ) : UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.HeatAgeMass c := by
  unfold HeatAgeMass
  intro g
  have hcpos : ∀ x : ℝ × ℝ, x ∈ strip c → 0 < c := by
    intro x hx
    simp only [strip, Set.mem_prod, Set.mem_Ioc] at hx
    exact lt_of_lt_of_le hx.1.1 hx.1.2
  have hae : ∀ᵐ x ∂(cellMeasure c), x ∈ UnforcedLeray.B0220.cell c :=
    ae_restrict_mem (measurableSet_cell c)
  have hac : cellMeasure c ≪ measureH c := by
    unfold measureH
    refine withDensity_absolutelyContinuous' measurable_weightH.aemeasurable ?_
    filter_upwards [hae] with x hx
    have hx1 : (0 : ℝ) < x.1 := by
      simp only [UnforcedLeray.B0220.cell, Set.mem_prod, Set.mem_Ioi] at hx
      exact hx.1
    unfold weightH
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hx1 _)).ne'
  have hGm : AEStronglyMeasurable (g : Profile → MeridC) (measureH c) :=
    Lp.aestronglyMeasurable g
  have hGc : AEStronglyMeasurable (g : Profile → MeridC) (cellMeasure c) :=
    hGm.mono_ac hac
  have hGp : AEStronglyMeasurable (g : Profile → MeridC)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (strip c))) := by
    rw [← cellMeasure_eq_prod']
    exact hGc
  have hsq : AEMeasurable (fun p : Profile => ‖(g : Profile → MeridC) p‖ₑ ^ 2) (cellMeasure c) :=
    hGc.aemeasurable.enorm.pow_const 2
  have hLHS : ∫⁻ p, ‖(g : Profile → MeridC) p‖ₑ ^ 2 ∂measureH c
      = ∫⁻ p, weightH p * ‖(g : Profile → MeridC) p‖ₑ ^ 2 ∂cellMeasure c := by
    exact lintegral_withDensity_eq_lintegral_mul₀ (μ := cellMeasure c)
      measurable_weightH.aemeasurable hsq
  have hprod : ∫⁻ p, weightH p * ‖(g : Profile → MeridC) p‖ₑ ^ 2 ∂cellMeasure c
      = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ z in strip c,
          ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * ‖(g : Profile → MeridC) (s, z)‖ₑ ^ 2 := by
    rw [cellMeasure_eq_prod']
    have hf : AEMeasurable (fun p : Profile => weightH p * ‖(g : Profile → MeridC) p‖ₑ ^ 2)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (strip c))) :=
      measurable_weightH.aemeasurable.mul (hGp.aemeasurable.enorm.pow_const 2)
    refine (lintegral_prod _ hf).trans ?_
    rfl
  rw [hLHS, hprod]
  refine lintegral_congr fun s => ?_
  simp only [stripM, fibre]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  refine setLIntegral_congr_fun (measurableSet_strip c) fun z hz => ?_
  rw [periodize_slice_of_mem (hcpos z hz) (g : Profile → MeridC) s hz]
