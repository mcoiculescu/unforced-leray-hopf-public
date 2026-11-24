import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1_of
import UnforcedLeray.Units.B0289.Periodize
import UnforcedLeray.Units.B0224.FiberHeat
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Units.B0220.Chart
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `PlaneHeatAeDatum` holds (decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1`)

Source `the November 2 reference manuscript`
lines 1684-1689, 3426-3430: the plane heat at positive time only sees the a.e.-class of its datum.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

theorem planeHeatAeDatum_holds :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.PlaneHeatAeDatum := by
  intro c hc f' G hper hae
  -- (1) the a.e. identity on the cell `B0220.cellMeasure c = volume.restrict (cell c)`
  have hae' : ∀ᵐ p ∂((UnforcedLeray.B0220.cellMeasure c).withDensity UnforcedLeray.B0220.weightH),
      (UnforcedLeray.Short.PartIIa.PepsC 0 c f' : UnforcedLeray.B0220.Profile →
        UnforcedLeray.B0223.MeridC) p = G p := hae
  have hcell : ∀ᵐ p ∂(UnforcedLeray.B0220.cellMeasure c),
      (UnforcedLeray.Short.PartIIa.PepsC 0 c f' : UnforcedLeray.B0220.Profile →
        UnforcedLeray.B0223.MeridC) p = G p := by
    have h1 := (MeasureTheory.ae_withDensity_iff UnforcedLeray.B0220.measurable_weightH).1 hae'
    have h2 : ∀ᵐ p ∂(UnforcedLeray.B0220.cellMeasure c), p ∈ UnforcedLeray.B0220.cell c :=
      MeasureTheory.ae_restrict_mem (UnforcedLeray.B0220.measurableSet_cell c)
    filter_upwards [h1, h2] with p hp1 hp2
    apply hp1
    have hpos : (0 : ℝ) < p.1 := by
      have h := hp2
      simp only [UnforcedLeray.B0220.cell, Set.mem_prod, Set.mem_Ioi] at h
      exact h.1
    unfold UnforcedLeray.B0220.weightH
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpos _)).ne'
  -- (2) Fubini on the product cell `(volume.restrict (Ioi 0)).prod (volume.restrict (strip c))`
  have hprod := hcell
  rw [UnforcedLeray.B0224.cellMeasure_eq_prod' c] at hprod
  have hσ : ∀ᵐ σ ∂(volume : Measure ℝ), 0 < σ →
      ∀ᵐ z ∂(volume.restrict (UnforcedLeray.B0224.strip c)),
        (UnforcedLeray.Short.PartIIa.PepsC 0 c f' : UnforcedLeray.B0220.Profile →
          UnforcedLeray.B0223.MeridC) (σ, z) = G (σ, z) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).1
      (MeasureTheory.Measure.ae_ae_of_ae_prod hprod)
  filter_upwards [hσ] with σ hσσ
  intro hpos θ hθ
  have hz := hσσ hpos
  -- (3) the periodized datum agrees with `σ⁻¹ G(σ, ·)` a.e. on the cylinder
  set P : ℝ × ℝ → Prop := fun z =>
    UnforcedLeray.B0220.periodize c (UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.sfcGp hc f') (σ, z)
      = ((σ : ℝ) : ℂ)⁻¹ • G (σ, z) with hPdef
  have hpa : ∀ z : ℝ × ℝ,
      UnforcedLeray.B0220.periodize c (UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.sfcGp hc f')
        (σ, (z.1 + c, z.2)) =
      UnforcedLeray.B0220.periodize c (UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.sfcGp hc f')
        (σ, z) := by
    intro z
    simp only [UnforcedLeray.B0220.periodize, UnforcedLeray.B0220.reduceIoc_add hc]
  have hG' : ∀ z : ℝ × ℝ, G (σ, (z.1 + c, z.2)) = G (σ, z) := fun z => hper σ z.1 z.2
  have hperP : UnforcedLeray.B0284.IsQPeriodic c P := by
    intro z
    show (UnforcedLeray.B0220.periodize c (UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.sfcGp hc f')
        (σ, (z.1 + c, z.2)) = ((σ : ℝ) : ℂ)⁻¹ • G (σ, (z.1 + c, z.2))) =
      (UnforcedLeray.B0220.periodize c (UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.sfcGp hc f')
        (σ, z) = ((σ : ℝ) : ℂ)⁻¹ • G (σ, z))
    rw [hpa z, hG' z]
  have hcellP : ∀ᵐ z ∂(UnforcedLeray.B0284.cellMeasure c), P z := by
    unfold UnforcedLeray.B0284.cellMeasure
    refine MeasureTheory.Measure.ae_smul_measure ?_ _
    filter_upwards [hz, MeasureTheory.ae_restrict_mem (UnforcedLeray.B0224.measurableSet_strip c)]
      with z hzq hzs
    show UnforcedLeray.B0220.periodize c (UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.sfcGp hc f')
        (σ, z) = ((σ : ℝ) : ℂ)⁻¹ • G (σ, z)
    rw [UnforcedLeray.B0224.periodize_slice_of_mem hc _ σ hzs]
    simp only [UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.sfcGp, hzq]
  have hae2 : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), P z :=
    UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hperP hcellP
  -- (4) the Gaussian average only sees the a.e. class (measure-preserving translation)
  funext x
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ, UnforcedLeray.B0224.planeHeat_of_pos hθ]
  refine MeasureTheory.integral_congr_ae ?_
  have hmp : MeasurePreserving (fun y : UnforcedLeray.Gaussian.Euc 2 =>
      x - UnforcedLeray.B0224.planeι y) (volume : Measure (UnforcedLeray.Gaussian.Euc 2))
      (volume : Measure (ℝ × ℝ)) :=
    (Measure.measurePreserving_sub_left (volume : Measure (ℝ × ℝ)) x).comp
      ((MeasureTheory.volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2)))
  filter_upwards [hmp.quasiMeasurePreserving.ae
    (p := fun z => P z) hae2] with y hy
  have hy' : UnforcedLeray.B0220.periodize c (UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.sfcGp hc f')
        (σ, x - UnforcedLeray.B0224.planeι y) = ((σ : ℝ) : ℂ)⁻¹ • G (σ, x - UnforcedLeray.B0224.planeι y) := hy
  rw [hy']
