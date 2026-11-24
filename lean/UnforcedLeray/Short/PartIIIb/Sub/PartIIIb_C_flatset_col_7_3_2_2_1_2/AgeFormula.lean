import UnforcedLeray.Units.B0224.FiberHeat
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

open UnforcedLeray.B0220 (HSpace measureH Profile cellMeasure)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0224 (planeHeat strip heatH heatTime measurable_heatTime fiberHeat
  stronglyMeasurable_fiberHeat cellMeasure_eq_prod' lintegral_measureH_eq periodize_slice_of_mem measurableSet_strip
  coeFn_heatH)
open UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong

theorem heatAgeFormula_holds (c : ℝ) :
    UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.HeatAgeFormula c := by
  intro hc ν t g
  have hθm : Measurable (heatTime ν t) := measurable_heatTime ν t
  set θ : ℝ → ℝ := heatTime ν t with hθdef
  have hF : StronglyMeasurable (fiberHeat c θ (g : Profile → MeridC)) :=
    stronglyMeasurable_fiberHeat hθm (Lp.stronglyMeasurable g)
  set Φ : Profile → ℝ≥0∞ := fun p => ‖fiberHeat c θ (g : Profile → MeridC) p - (g : Profile → MeridC) p‖ₑ ^ 2
    with hΦdef
  have hΦ : Measurable Φ :=
    ((hF.sub (Lp.stronglyMeasurable g)).measurable.enorm).pow_const 2
  -- Step A: the error of `heatH g - g` agrees a.e. with the fibre error.
  have hA : ∫⁻ p, ‖((heatH hc hθm g - g : HSpace c MeridC) : Profile → MeridC) p‖ₑ ^ 2 ∂measureH c
      = ∫⁻ p, Φ p ∂measureH c := by
    refine lintegral_congr_ae ?_
    filter_upwards [coeFn_heatH hc hθm g, Lp.coeFn_sub (heatH hc hθm g) g] with p hp1 hp2
    rw [hp2, Pi.sub_apply, hp1]
  -- Step B: the mass in `H` is an integral over the cell.
  have hB : ∫⁻ p, Φ p ∂measureH c
      = ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * Φ p ∂cellMeasure c :=
    lintegral_measureH_eq Φ hΦ
  -- Step C: split the cell as a product and integrate in the age first.
  have hw : Measurable fun p : Profile => ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst).pow_const _)
  have hC : ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * Φ p ∂cellMeasure c
      = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
          ∫⁻ z in strip c, Φ (s, z) := by
    rw [cellMeasure_eq_prod', lintegral_prod (fun p : Profile => ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * Φ p)
      (hw.mul hΦ).aemeasurable]
    refine lintegral_congr fun s => ?_
    have hm : Measurable fun z : ℝ × ℝ => Φ (s, z) := hΦ.comp measurable_prodMk_left
    dsimp only
    rw [lintegral_const_mul _ hm]
  -- Step D: on the strip, the Profile error is the planar fibre error.
  have hD : ∀ s : ℝ, ∫⁻ z in strip c, Φ (s, z) =
      stripN c (heatTime ν t s) (fibre c g s) := by
    intro s
    unfold stripN
    refine setLIntegral_congr_fun (measurableSet_strip c) fun z hz => ?_
    have hfib : fibre c g s z = (g : Profile → MeridC) (s, z) :=
      periodize_slice_of_mem hc (g : Profile → MeridC) s hz
    show ‖fiberHeat c θ (g : Profile → MeridC) (s, z) - (g : Profile → MeridC) (s, z)‖ₑ ^ 2
      = ‖planeHeat (heatTime ν t s) (fibre c g s) z - fibre c g s z‖ₑ ^ 2
    rw [hfib]
    rfl
  rw [hA, hB, hC]
  refine lintegral_congr fun s => ?_
  rw [hD s]
