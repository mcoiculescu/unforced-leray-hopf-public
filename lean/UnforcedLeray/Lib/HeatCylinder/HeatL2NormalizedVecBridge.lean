import UnforcedLeray.Lib.HeatCylinder.HeatL2PlaneCenteredBridge
import UnforcedLeray.Lib.HeatCylinder.PeriodicLift

/-!
# Normalized-cell to centered-cell vector `L²`

A normalized-cell vector class is lifted by the actual `(0,c]` periodic extension. The same
periodic field then represents it on the centered train cell, with the exact factor `c` in the
squared norms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)
open UnforcedLeray.Cyl (cellμ)

/-- A globally measurable representative chosen from a normalized-cell vector `L²` class. -/
noncomputable def normalizedVecRep {c : ℝ}
    (x : Lp Vec 2 (cellMeasure c)) : Plane → Vec :=
  (Lp.aestronglyMeasurable x).mk (x : Plane → Vec)

theorem normalizedVecRep_measurable {c : ℝ} (x : Lp Vec 2 (cellMeasure c)) :
    Measurable (normalizedVecRep x) :=
  (Lp.aestronglyMeasurable x).measurable_mk

theorem normalizedVecRep_ae {c : ℝ} (x : Lp Vec 2 (cellMeasure c)) :
    normalizedVecRep x =ᵐ[cellMeasure c] (x : Plane → Vec) :=
  (Lp.aestronglyMeasurable x).ae_eq_mk.symm

/-- The measurable, periodic extension of a normalized-cell vector representative. -/
noncomputable def normalizedVecPeriodicRep {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) : Plane → Vec :=
  perLift hc (normalizedVecRep x)

theorem normalizedVecPeriodicRep_measurable {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) : Measurable (normalizedVecPeriodicRep hc x) :=
  measurable_perLift hc (normalizedVecRep_measurable x)

theorem normalizedVecPeriodicRep_periodic {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) : UnforcedLeray.Cyl.IsPeriodic c
      (normalizedVecPeriodicRep hc x) :=
  perLift_periodic hc (normalizedVecRep x)

theorem normalizedVecPeriodicRep_cell_ae {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) :
    normalizedVecPeriodicRep hc x =ᵐ[cellMeasure c] (x : Plane → Vec) := by
  exact (perLift_ae_eq_cell hc (normalizedVecRep x)).trans (normalizedVecRep_ae x)

theorem memLp_normalizedVecPeriodicRep_centered {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) : MemLp (normalizedVecPeriodicRep hc x) 2 (cellμ c) := by
  have hcell : MemLp (normalizedVecPeriodicRep hc x) 2 (cellMeasure c) := by
    refine ⟨(normalizedVecPeriodicRep_measurable hc x).aestronglyMeasurable.mono_ac
      (UnforcedLeray.B0284.cellMeasure_ac c), ?_⟩
    rw [eLpNorm_congr_ae (normalizedVecPeriodicRep_cell_ae hc x)]
    exact (Lp.memLp x).2
  exact memLp_cyl_of_memLp_cellMeasure hc
    (normalizedVecPeriodicRep_measurable hc x)
    (normalizedVecPeriodicRep_periodic hc x) hcell

/-- The concrete centered-cell class represented by the periodic extension of normalized data. -/
noncomputable def centeredVecOfNormalizedVec {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) : UnforcedLeray.Cyl.L2v c :=
  (memLp_normalizedVecPeriodicRep_centered hc x).toLp (normalizedVecPeriodicRep hc x)

@[simp] theorem centeredVecOfNormalizedVec_coe_ae {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) :
    (centeredVecOfNormalizedVec hc x : Plane → Vec) =ᵐ[cellμ c]
      normalizedVecPeriodicRep hc x :=
  (memLp_normalizedVecPeriodicRep_centered hc x).coeFn_toLp

/-- Exact normalized-to-centered squared norm conversion for the transported quotient class. -/
theorem norm_sq_centeredVecOfNormalizedVec {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) :
    ‖centeredVecOfNormalizedVec hc x‖ ^ 2 = c * ‖x‖ ^ 2 := by
  have hscale := eLpNorm_sq_cyl_eq_cellMeasure hc
    (normalizedVecPeriodicRep_measurable hc x)
    (normalizedVecPeriodicRep_periodic hc x)
  have hcenter : eLpNorm
      (centeredVecOfNormalizedVec hc x : Plane → Vec) 2 (cellμ c) =
        eLpNorm (normalizedVecPeriodicRep hc x) 2 (cellμ c) :=
    eLpNorm_congr_ae (centeredVecOfNormalizedVec_coe_ae hc x)
  have hnorm : eLpNorm (normalizedVecPeriodicRep hc x) 2 (cellMeasure c) =
      eLpNorm (x : Plane → Vec) 2 (cellMeasure c) :=
    eLpNorm_congr_ae (normalizedVecPeriodicRep_cell_ae hc x)
  have hsq := congrArg ENNReal.toReal hscale
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hc),
    ENNReal.toReal_pow] at hsq
  rw [Lp.norm_def, Lp.norm_def, hcenter]
  rw [hnorm] at hsq
  exact hsq

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.memLp_normalizedVecPeriodicRep_centered
#print axioms UnforcedLeray.HeatCylinder.norm_sq_centeredVecOfNormalizedVec
