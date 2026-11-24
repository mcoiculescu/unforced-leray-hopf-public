import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_2
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellPairF
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellHolder
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeTotalLinear

/-!
# Integrability helper for `gl_pairLinR` and `gl_pairLinL`

A field `u ∈ Y_r` (`r > 1`) lies in `L^r` of one phase cell, and a phase test lies in the conjugate
`L^{r'}`; Hölder then gives integrability of `dotL (Φ x) (u x)` on the cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- A field of finite phase `L^r` norm lies in `L^r` of one phase cell. -/
theorem memLp_phaseCell_of_phaseLpNorm {P r : ℝ} (hP : 0 < P) (hr : 0 < r)
    {f : ℝ × Space → CVec3} (hm : AEStronglyMeasurable f volume)
    (hfin : phaseLpNorm P r f < ⊤) :
    MemLp f (ENNReal.ofReal r) (volume.restrict (phaseCell P)) := by
  refine ⟨hm.restrict, ?_⟩
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr.le]
  have hprod : (volume : Measure (ℝ × Space)).restrict (phaseCell P) =
      ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space) := by
    simpa [phaseCell, Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Space)) (Ioc (0 : ℝ) P)).symm
  have hae : AEMeasurable (fun z : ℝ × Space => ‖f z‖ₑ ^ r) (volume.restrict (phaseCell P)) :=
    (AEMeasurable.pow_const (AEStronglyMeasurable.enorm hm) r).mono_measure Measure.restrict_le_self
  have hI : ∫⁻ z, ‖f z‖ₑ ^ r ∂(volume.restrict (phaseCell P)) =
      ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖f (t, y)‖ₑ ^ r := by
    rw [hprod] at hae ⊢
    rw [lintegral_prod _ hae]
  have hPne : ENNReal.ofReal P⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hP)).ne'
  have hfin' := hfin
  unfold phaseLpNorm at hfin'
  rw [ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.2 hr)] at hfin'
  have hJ : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖f (t, y)‖ₑ ^ r < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right hfin'.ne hPne
  rw [hI]
  exact ENNReal.rpow_lt_top_of_nonneg (one_div_pos.2 hr).le hJ.ne

/-- Integrability of `dotL (Φ x) (u x)` on one phase cell for a phase test `Φ` and `u ∈ Y_r`,
`r > 1`. -/
theorem integrable_dotL_phaseTest_Yr {P r : ℝ} (hP : 0 < P) (hr : 1 < r)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {u : ℝ × Space → CVec3} (hu : IsInYr P r u) :
    Integrable (fun x => dotL (Φ x) (u x)) (volume.restrict (phaseCell P)) := by
  have : Fact (0 < P) := ⟨hP⟩
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨ENNReal.one_le_ofReal.2 hr.le⟩
  have hq : 1 < ENNReal.ofReal r := ENNReal.one_lt_ofReal.2 hr
  have hΦm : MemLp Φ (conjExp (ENNReal.ofReal r)) (volume.restrict (phaseCell P)) :=
    memLp_phaseTest_cell (r := conjExp (ENNReal.ofReal r)) (conjExp_ne_top hq) hΦ
  have hum : MemLp u (ENNReal.ofReal r) (volume.restrict (phaseCell P)) :=
    memLp_phaseCell_of_phaseLpNorm hP (by linarith) hu.meas hu.finite
  exact integrable_dotL_of_memLp_holder hΦm hum

end UnforcedLeray.Short.IIb
