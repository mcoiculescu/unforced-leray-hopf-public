import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_1.Weight

/-!
# Density of the class `s^{3/4} φ` in `H` (tex lines 1650-1656)

`F ↦ s^{-3/4} F` is an isometry from `H` onto `L²(cellMeasure c)` (`Weight.lean`). Approximating
`G = 1_cell · s^{-3/4} f` in unweighted `L²(volume)` by a continuous compactly supported `φ`
(`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`) gives `‖f - s^{3/4} φ‖_H ≤ ε`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.DilStrong

open UnforcedLeray.B0220 (HSpace measureH Profile cellMeasure cell)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete.DilWeight

theorem dilDenseGood_holds (c : ℝ) (hc : 0 < c) : UnforcedLeray.Short.PartIIIb.Concrete.DilStrong.DilDenseGood c := by
  intro f ε hε
  have hF : StronglyMeasurable (⇑f) := Lp.stronglyMeasurable f
  have hrm : Measurable fun p : Profile => p.1 ^ (-(3 / 4 : ℝ)) := measurable_fst.pow_const _
  have hwm : Measurable fun p : Profile => p.1 ^ (3 / 4 : ℝ) := measurable_fst.pow_const _
  have hGsm : StronglyMeasurable (fun p : Profile => p.1 ^ (-(3 / 4 : ℝ)) • f p) :=
    hrm.stronglyMeasurable.smul hF
  have hGmem : MemLp (fun p : Profile => p.1 ^ (-(3 / 4 : ℝ)) • f p) 2 (cellMeasure c) := by
    refine ⟨hGsm.aestronglyMeasurable, ?_⟩
    rw [← eLpNorm_measureH_eq_weighted hF]
    exact (Lp.memLp f).2
  have hGc : MemLp ((cell c).indicator (fun p : Profile => p.1 ^ (-(3 / 4 : ℝ)) • f p))
      2 (volume : Measure Profile) :=
    (memLp_indicator_iff_restrict (UnforcedLeray.B0220.measurableSet_cell c)).2 hGmem
  obtain ⟨phi, hsupp, hbd, hcont, hmemvol⟩ :=
    MemLp.exists_hasCompactSupport_eLpNorm_sub_le (μ := (volume : Measure Profile)) (p := 2)
      ENNReal.ofNat_ne_top hGc (ENNReal.ofReal_pos.2 (by linarith : (0 : ℝ) < ε / 2)).ne'
  have hsmW : StronglyMeasurable (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p) :=
    hwm.stronglyMeasurable.smul hcont.stronglyMeasurable
  have hmemH : MemLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p) 2 (measureH c) := by
    refine ⟨hsmW.aestronglyMeasurable, ?_⟩
    have hae : (fun p : Profile => p.1 ^ (-(3 / 4 : ℝ)) • (p.1 ^ (3 / 4 : ℝ) • phi p))
        =ᵐ[cellMeasure c] phi := by
      filter_upwards [ae_restrict_mem (UnforcedLeray.B0220.measurableSet_cell c)] with p hp
      exact weight_cancel (show 0 < p.1 from hp.1) (phi p)
    rw [eLpNorm_measureH_eq_weighted hsmW]
    refine lt_of_eq_of_lt (eLpNorm_congr_ae hae) ?_
    exact lt_of_le_of_lt (eLpNorm_mono_measure _ Measure.restrict_le_self) hmemvol.2
  refine ⟨phi, hcont, hsupp, hmemH, ?_⟩
  have hc1 : (⇑(f - hmemH.toLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p))) =ᵐ[measureH c]
      fun p : Profile => f p - p.1 ^ (3 / 4 : ℝ) • phi p := by
    filter_upwards [Lp.coeFn_sub f (hmemH.toLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p)),
      MemLp.coeFn_toLp hmemH] with p h1 h2
    rw [h1, Pi.sub_apply, h2]
  have hsmD : StronglyMeasurable (fun p : Profile => f p - p.1 ^ (3 / 4 : ℝ) • phi p) :=
    hF.sub hsmW
  have hfin : eLpNorm (⇑(f - hmemH.toLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p))) 2
      (measureH c) ≤ ENNReal.ofReal (ε / 2) := by
    refine le_trans (le_of_eq (eLpNorm_congr_ae hc1)) ?_
    rw [eLpNorm_measureH_eq_weighted hsmD]
    have h2 : (fun p : Profile => p.1 ^ (-(3 / 4 : ℝ)) • (f p - p.1 ^ (3 / 4 : ℝ) • phi p))
        =ᵐ[cellMeasure c]
        fun p : Profile => (cell c).indicator (fun q : Profile => q.1 ^ (-(3 / 4 : ℝ)) • f q) p
          - phi p := by
      filter_upwards [ae_restrict_mem (UnforcedLeray.B0220.measurableSet_cell c)] with p hp
      rw [Set.indicator_of_mem hp, smul_sub, weight_cancel (show 0 < p.1 from hp.1) (phi p)]
    refine le_trans (le_of_eq (eLpNorm_congr_ae h2)) ?_
    refine le_trans (eLpNorm_mono_measure _ (show cellMeasure c ≤ volume from Measure.restrict_le_self))
      ?_
    exact hbd
  rw [Lp.norm_def]
  calc (eLpNorm (⇑(f - hmemH.toLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p))) 2
          (measureH c)).toReal
      ≤ (ENNReal.ofReal (ε / 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfin
    _ = ε / 2 := ENNReal.toReal_ofReal (by linarith)
    _ < ε := by linarith

end UnforcedLeray.Short.PartIIIb.Concrete.DilStrong
