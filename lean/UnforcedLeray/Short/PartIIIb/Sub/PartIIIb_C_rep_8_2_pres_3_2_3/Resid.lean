import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_3.Equiv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_4
import UnforcedLeray.Short.PartIIb.Sub.R1_7
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R04ResidualPeriodic

/-!
# The raw residual `F_R` of a level: continuity off the axis and periodicity (`pres/3/2/3`)

Source `the November 2 reference manuscript`:
1205-1225 (Proposition `sct:lift`), 1263 (`F_R = s^{3/2} r`), 2051 (`c`-periodic train).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem pf3_rawResidF_contOn (Pl : PlanarData) (L : ReturnLevel) (hR : 2 ≤ L.ε⁻¹) :
    ContinuousOn (fun x : ℝ × Space => rawResidF Pl L x.1 x.2) offAxisSet := by
  have hνpos : 0 < L.ν := L.ν_pos
  have hψ : ContDiffOn ℝ 3 (UnforcedLeray.Short.IIb.trainStream (L.params Pl))
      UnforcedLeray.B0185.ageDomain :=
    (UnforcedLeray.Short.IIb.trainStreamSmoothBUC_of UnforcedLeray.Short.PartI.trainStreamSmooth
      L.ν (cOf L.ν) hνpos (cOf_pos hνpos) L.train L.train_buc).of_le (by simp)
  have hpr : ContDiffOn ℝ 2 (UnforcedLeray.Short.IIb.trainPressure (L.params Pl))
      UnforcedLeray.B0185.ageDomain :=
    (UnforcedLeray.Short.IIb.trainPressureSmooth L.ν (cOf L.ν) L.train).of_le (by simp)
  have hRR : 2 ≤ (L.params Pl).R := hR
  exact pf4_ringResidual_contOn (L.params Pl).R L.ν _ _ hRR hψ hpr

theorem pf3_rawResidF_periodic (Pl : PlanarData) (L : ReturnLevel) (hR : 2 ≤ L.ε⁻¹) (τ : ℝ) :
    rawResidF Pl L (τ + 2 * L.ε * cOf L.ν) = rawResidF Pl L τ := by
  have hRR : 2 ≤ (L.params Pl).R := hR
  have e : 2 * L.ε * cOf L.ν = 2 * cOf L.ν / (L.params Pl).R := by
    show 2 * L.ε * cOf L.ν = 2 * cOf L.ν / L.ε⁻¹
    field_simp
  unfold rawResidF
  rw [e]
  exact UnforcedLeray.Short.PartIIa.ringResidual_periodic _ _ _ hRR _ _
    (UnforcedLeray.B0190.qPeriodicOn_trainStream L.train)
    (UnforcedLeray.B0190.qPeriodicOn_trainPressure L.train) τ

end UnforcedLeray.Short.PartIIIb.Concrete
