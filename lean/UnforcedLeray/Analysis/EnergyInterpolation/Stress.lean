import UnforcedLeray.Statement
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-!
# Genuine integrability of the quadratic stress

The actual products of velocity components belong to L^(5/3) whenever the
vector velocity belongs to L^(10/3), on the same measure space. Hölder supplies
both membership and the quantitative norm bound. In particular the result
applies to the actual space-time slab and its Lebesgue measure.
No pressure operator or Riesz transform estimate is assumed here.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.EnergyInterpolation

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Coordinate evaluation preserves actual Lᵖ membership. -/
theorem coordinate_memLp {u : α → Space} {p : ℝ≥0∞}
    (hu : MemLp u p μ) (i : Fin 3) : MemLp (fun z => u z i) p μ :=
  hu.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i)

/-- A coordinate is pointwise dominated by the Euclidean vector norm. -/
theorem eLpNorm_coordinate_le (u : α → Space) (p : ℝ≥0∞) (i : Fin 3) :
    eLpNorm (fun z => u z i) p μ ≤ eLpNorm u p μ :=
  eLpNorm_mono (fun z => PiLp.norm_apply_le (u z) i)

/-- The exact Hölder relation for the quadratic Navier--Stokes stress. -/
theorem holder_tenThirds_tenThirds :
    ENNReal.HolderTriple (10 / 3) (10 / 3) (5 / 3) := by
  apply ENNReal.HolderTriple.of_toReal
  norm_num [Real.holderTriple_iff, ENNReal.toReal_div]

/-- Genuine L^(5/3) membership of each quadratic stress component. -/
theorem stress_memLp_fiveThirds {u : α → Space}
    (hu : MemLp u (10 / 3) μ) (i j : Fin 3) :
    MemLp (fun z => u z i * u z j) (5 / 3) μ := by
  let : ENNReal.HolderTriple (10 / 3) (10 / 3) (5 / 3) := holder_tenThirds_tenThirds
  exact (coordinate_memLp hu j).mul' (coordinate_memLp hu i)

/-- Hölder's bound has constant one in the vector velocity norm. -/
theorem eLpNorm_stress_le {u : α → Space}
    (hu : MemLp u (10 / 3) μ) (i j : Fin 3) :
    eLpNorm (fun z => u z i * u z j) (5 / 3) μ ≤ (eLpNorm u (10 / 3) μ) ^ 2 := by
  let : ENNReal.HolderTriple (10 / 3) (10 / 3) (5 / 3) := holder_tenThirds_tenThirds
  have h := eLpNorm_smul_le_mul_eLpNorm
    (coordinate_memLp hu j).aestronglyMeasurable
    (coordinate_memLp hu i).aestronglyMeasurable
    (p := (10 / 3 : ℝ≥0∞)) (q := (10 / 3 : ℝ≥0∞)) (r := (5 / 3 : ℝ≥0∞))
  calc
    _ ≤ eLpNorm (fun z => u z i) (10 / 3) μ *
        eLpNorm (fun z => u z j) (10 / 3) μ := h
    _ ≤ eLpNorm u (10 / 3) μ * eLpNorm u (10 / 3) μ := by
      exact mul_le_mul (eLpNorm_coordinate_le u _ i) (eLpNorm_coordinate_le u _ j)
        zero_le zero_le
    _ = _ := (pow_two _).symm

/-- The finite real-valued L^(5/3) stress norm is bounded by the squared
finite L^(10/3) vector norm. -/
theorem stress_norm_le {u : α → Space}
    (hu : MemLp u (10 / 3) μ) (i j : Fin 3) :
    (eLpNorm (fun z => u z i * u z j) (5 / 3) μ).toReal ≤
      (eLpNorm u (10 / 3) μ).toReal ^ 2 := by
  have hfinite : (eLpNorm u (10 / 3) μ) ^ 2 ≠ ⊤ := by finiteness [hu.2]
  simpa only [ENNReal.toReal_pow] using
    ENNReal.toReal_mono hfinite (eLpNorm_stress_le hu i j)

/-- Each actual space-time stress component has the pressure forcing exponent
on the entire physical slab, under actual L^(10/3) velocity membership. -/
theorem spacetime_stress_memLp_fiveThirds {u : Velocity} {T : ℝ}
    (hu : MemLp (fun z : SpaceTime => u z.1 z.2) (10 / 3)
      (volume.restrict (slab T))) (i j : Fin 3) :
    MemLp (fun z : SpaceTime => u z.1 z.2 i * u z.1 z.2 j) (5 / 3)
      (volume.restrict (slab T)) :=
  stress_memLp_fiveThirds hu i j

/-- The corresponding slab norm estimate uses the same actual functions. -/
theorem spacetime_stress_eLpNorm_le {u : Velocity} {T : ℝ}
    (hu : MemLp (fun z : SpaceTime => u z.1 z.2) (10 / 3)
      (volume.restrict (slab T))) (i j : Fin 3) :
    eLpNorm (fun z : SpaceTime => u z.1 z.2 i * u z.1 z.2 j) (5 / 3)
      (volume.restrict (slab T)) ≤
      (eLpNorm (fun z : SpaceTime => u z.1 z.2) (10 / 3)
        (volume.restrict (slab T))) ^ 2 :=
  eLpNorm_stress_le hu i j

end UnforcedLeray.EnergyInterpolation
