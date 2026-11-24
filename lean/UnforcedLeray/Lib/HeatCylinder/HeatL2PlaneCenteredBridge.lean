import UnforcedLeray.Lib.HeatCylinder.HeatL2PlaneTranslation
import UnforcedLeray.Lib.HeatCylinder.HeatL2Operator
import UnforcedLeray.Lib.HeatCylinder.CellBridge
import UnforcedLeray.Lib.TrainB.VecBridge

/-!
# Transport normalized Plane heat data to the centered vector cylinder

This leaf keeps the concrete periodic representative and the cell normalization visible while
connecting the B0284 Plane-valued L² quotient to Train's centered Euclidean-vector L² carrier.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)
open UnforcedLeray.Cyl (cellμ)

/-- The selected normalized Plane representative, converted pointwise to Train's Euclidean
vector coordinates. -/
def normalizedPlaneVecRep {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) : Plane → Vec :=
  fun z => UnforcedLeray.Train.toVec (planeRep hc x z)

theorem normalizedPlaneVecRep_measurable {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) : Measurable (normalizedPlaneVecRep hc x) := by
  exact UnforcedLeray.Train.toVecL.continuous.measurable.comp (planeRep_spec hc x).1

theorem normalizedPlaneVecRep_periodic {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) : UnforcedLeray.Cyl.IsPeriodic c
      (normalizedPlaneVecRep hc x) := by
  exact UnforcedLeray.TrainB.periodic_vecFieldOfPlane (planeRep_spec hc x).2.1

theorem memLp_normalizedPlaneVecRep {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) : MemLp (normalizedPlaneVecRep hc x) 2 (cellμ c) := by
  have hnorm : MemLp (normalizedPlaneVecRep hc x) 2 (cellMeasure c) := by
    refine ⟨(normalizedPlaneVecRep_measurable hc x).aestronglyMeasurable.mono_ac
      (UnforcedLeray.B0284.cellMeasure_ac c), ?_⟩
    have hcoordinate := UnforcedLeray.TrainB.eLpNorm_vecFieldOfPlane_le
      (c := c) (p := (2 : ℝ≥0∞)) (u := planeRep hc x)
    have hrep := (planeRep_spec hc x).2.2
    have hfinite : eLpNorm (planeRep hc x) 2 (cellMeasure c) < ⊤ := by
      rw [eLpNorm_congr_ae hrep]
      exact (Lp.memLp x).2
    have hfactor : ENNReal.ofReal
        ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ < ⊤ := ENNReal.ofReal_lt_top
    exact lt_of_le_of_lt hcoordinate (ENNReal.mul_lt_top hfactor hfinite)
  exact UnforcedLeray.HeatCylinder.memLp_cyl_of_memLp_cellMeasure hc
    (normalizedPlaneVecRep_measurable hc x)
    (normalizedPlaneVecRep_periodic hc x) hnorm

/-- The normalized Plane heat input, viewed as a centered-cell Euclidean-vector L² class. -/
noncomputable def centeredVecOfNormalizedPlane {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) : UnforcedLeray.Cyl.L2v c :=
  (memLp_normalizedPlaneVecRep hc x).toLp (normalizedPlaneVecRep hc x)

@[simp] theorem centeredVecOfNormalizedPlane_coe_ae {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) :
    (centeredVecOfNormalizedPlane hc x : Plane → Vec) =ᵐ[cellμ c]
      normalizedPlaneVecRep hc x :=
  (memLp_normalizedPlaneVecRep hc x).coeFn_toLp

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.normalizedPlaneVecRep_measurable
#print axioms UnforcedLeray.HeatCylinder.memLp_normalizedPlaneVecRep
#print axioms UnforcedLeray.HeatCylinder.centeredVecOfNormalizedPlane_coe_ae
