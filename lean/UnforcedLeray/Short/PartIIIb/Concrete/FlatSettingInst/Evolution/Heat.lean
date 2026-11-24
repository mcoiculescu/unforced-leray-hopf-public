import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.HeatConv
import UnforcedLeray.Lib.HeatCylinder.HeatVecTranslationBridge

/-!
# The physical heat family commutes with the reflection (source 2819-2836, 287-288)

Source of record: `the November 2 reference manuscript` (73 pages).

The free part of the Volterra iteration acts on the periodic lift of the cell datum:

* `periodicRepRefl : PeriodicRepRefl` (two periodic functions a.e. equal on the cell are a.e. equal
  on the plane, `periodic_ae_eq`);
* `heatS0Refl_of : PeriodicRepRefl → HeatS0Refl` (the planar heat kernel is even, `heat_refl`);
* `heatResponseRefl_of : PeriodicRepRefl → HeatResponseRefl` (its gradient is odd,
  `heatDiv_refl`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol

open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- The centered cylinder cell measure is the restricted Lebesgue measure of `B0579.cell`. -/
theorem cellμ_eq_restrict (c : ℝ) :
    UnforcedLeray.Cyl.cellμ c = volume.restrict (B0579.cell c) := by
  have h : UnforcedLeray.Cyl.cell c = B0579.cell c := by
    simp only [UnforcedLeray.Cyl.cell, B0579.cell, neg_div]
  rw [UnforcedLeray.Cyl.cellμ, h]

/-- Two `c`-periodic functions that agree a.e. on the cell agree a.e. on the plane. -/
theorem periodic_ae_eq {c : ℝ} (hc : 0 < c) {u v : ℝ × ℝ → ℝ}
    (hu : UnforcedLeray.Cyl.IsPeriodic c u) (hv : UnforcedLeray.Cyl.IsPeriodic c v)
    (h : u =ᵐ[volume.restrict (B0579.cell c)] v) : u =ᵐ[volume] v := by
  rw [← UnforcedLeray.HeatCylinder.centeredPerLift_eq_self_of_periodic hc hu,
    ← UnforcedLeray.HeatCylinder.centeredPerLift_eq_self_of_periodic hc hv]
  exact UnforcedLeray.HeatCylinder.centeredPerLift_congr_ae hc (by rw [cellμ_eq_restrict]; exact h)

/-- **`PeriodicRepRefl`**. -/
theorem periodicRepRefl : PeriodicRepRefl := by
  intro c m hc f
  have hrep : ∀ g : B0579.X c m,
      xColumnPeriodicRep hc g =ᵐ[volume.restrict (B0579.cell c)] (g : ℝ × ℝ → ℝ) := by
    intro g
    have := xColumnPeriodicRep_ae_eq hc g
    rwa [cellμ_eq_restrict] at this
  have hper : ∀ g : B0579.X c m, UnforcedLeray.Cyl.IsPeriodic c (xColumnPeriodicRep hc g) :=
    fun g => periodic_xColumnPeriodicRep hc g
  constructor
  · refine periodic_ae_eq hc (hper _) (fun z => ?_) ?_
    · show xColumnPeriodicRep hc f (-(z.1 + c, z.2)) = xColumnPeriodicRep hc f (-z)
      have h := hper f (-z.1 - c, -z.2)
      have e1 : (-(z.1 + c, z.2) : ℝ × ℝ) = (-z.1 - c, -z.2) := by
        ext
        · simp only [Prod.fst_neg]
          ring
        · simp only [Prod.snd_neg]
      have e2 : (-z : ℝ × ℝ) = ((-z.1 - c, -z.2).1 + c, (-z.1 - c, -z.2).2) := by
        ext
        · simp only [Prod.fst_neg]
          ring
        · simp only [Prod.snd_neg]
      rw [e1, e2, h]
    · have h1 := hrep (reflR c m f)
      have h2 := ae_cell_of_ae_cellMeasure (coeFn_reflR f)
      have h3 := (mp_neg_cell c).quasiMeasurePreserving.ae (hrep f)
      filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
      rw [hz1, hz2, hz3]
  · refine periodic_ae_eq hc (hper _) (fun z => by simp only [hper f z]) ?_
    have h2 := ae_cell_of_ae_cellMeasure (Lp.coeFn_neg f)
    filter_upwards [hrep (-f), h2, hrep f] with z hz1 hz2 hz3
    rw [hz1, hz2, Pi.neg_apply, hz3]

/-- **`HeatS0Refl`** from `PeriodicRepRefl` (the planar heat kernel is even). -/
theorem heatS0Refl_of (hP : PeriodicRepRefl) : HeatS0Refl := by
  intro c m _ hc1 hm t w
  change actualWeightedHeatS0Totalized hc1 hm t (reflV hm w) =
    reflV hm (actualWeightedHeatS0Totalized hc1 hm t w)
  by_cases ht0 : 0 ≤ t
  · by_cases ht1 : t ≤ 1
    · simp only [actualWeightedHeatS0Totalized, dif_pos ht0, dif_pos ht1]
      rcases eq_or_lt_of_le ht0 with h0 | hpos
      · subst h0
        simp only [actualWeightedHeatS0_zero, ContinuousLinearMap.id_apply]
      · refine Subtype.ext (Lp.ext ?_)
        rw [reflV_val, actualWeightedHeatS0_apply_of_pos hc1 hm hpos ht1,
          actualWeightedHeatS0_apply_of_pos hc1 hm hpos ht1, reflV_val]
        have hlift : xColumnHeatLift (Fact.out : 0 < c) (reflR c m w.1) =ᵐ[volume]
            fun z => xColumnHeatLift (Fact.out : 0 < c) w.1 (-z) := by
          filter_upwards [(hP c m Fact.out w.1).1] with z hz
          simp only [xColumnHeatLift, hz]
        filter_upwards [coeFn_xColumnHeatS0Positive Fact.out hm hpos ht1 (reflR c m w.1),
          coeFn_reflR (xColumnHeatS0Positive Fact.out hm hpos ht1 w.1),
          (mp_neg_cellMeasure c m).quasiMeasurePreserving.ae
            (coeFn_xColumnHeatS0Positive Fact.out hm hpos ht1 w.1)] with z h1 h2 h3
        rw [h1, h2, h3, heat_refl hpos hlift z]
    · simp only [actualWeightedHeatS0Totalized, dif_pos ht0, dif_neg ht1,
        ContinuousLinearMap.zero_apply, map_zero]
  · simp only [actualWeightedHeatS0Totalized, dif_neg ht0, ContinuousLinearMap.zero_apply, map_zero]

/-- **`HeatResponseRefl`** from `PeriodicRepRefl` (the gradient of the heat kernel is odd). -/
theorem heatResponseRefl_of (hP : PeriodicRepRefl) : HeatResponseRefl := by
  intro c m _ hc1 hm t F
  change actualWeightedHeatResponse hm t (reflF F) = reflV hm (actualWeightedHeatResponse hm t F)
  by_cases hpos : 0 < t
  · by_cases ht1 : t ≤ 1
    · refine Subtype.ext (Lp.ext ?_)
      rw [reflV_val, actualWeightedHeatResponse_value hm hpos ht1,
        actualWeightedHeatResponse_value hm hpos ht1]
      have hT : xFluxPeriodicTensor (Fact.out : 0 < c) (reflF F) =ᵐ[volume]
          fun z => -xFluxPeriodicTensor (Fact.out : 0 < c) F (-z) := by
        filter_upwards [(hP c m Fact.out (F 0)).1, (hP c m Fact.out (reflR c m (F 0))).2,
          (hP c m Fact.out (F 1)).1, (hP c m Fact.out (reflR c m (F 1))).2]
          with z h0 h0' h1 h1'
        simp only [xFluxPeriodicTensor, scalarFluxTensor, reflF_apply, h0', h1', h0, h1,
          Prod.neg_mk, neg_zero]
      filter_upwards [(memLp_xFlux_negativeHeatDiv_fst_X Fact.out hm hpos ht1 (reflF F)).coeFn_toLp,
        coeFn_reflR ((memLp_xFlux_negativeHeatDiv_fst_X Fact.out hm hpos ht1 F).toLp
          (fun z => (negativeHeatDiv t (xFluxPeriodicTensor Fact.out F) z).1)),
        (mp_neg_cellMeasure c m).quasiMeasurePreserving.ae
          (memLp_xFlux_negativeHeatDiv_fst_X Fact.out hm hpos ht1 F).coeFn_toLp] with z h1 h2 h3
      rw [h1, h2, h3]
      simp only [negativeHeatDiv, heatDiv_refl hpos hT z]
    · simp [actualWeightedHeatResponse, hpos, ht1]
  · simp [actualWeightedHeatResponse, hpos]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol
