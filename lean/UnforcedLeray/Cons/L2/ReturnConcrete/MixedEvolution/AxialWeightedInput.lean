import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatOperatorBound

/-!
# Axially weighted input in the normalized periodic heat carrier

An `X_m` column, multiplied by the q-periodic axial weight, is an actual normalized-cell L²
input for the cylinder Gaussian semigroup. This is the weighted/unweighted conjugation carrier
for the age-zero continuity argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0579 hiding Plane

private theorem cylCell_eq_restrict_radial {c : ℝ} :
    Cyl.cellμ c = volume.restrict (B0579.cell c) := by
  have hleft : -(c / 2) = -c / 2 := by ring
  simp [Cyl.cellμ, Cyl.cell, B0579.cell, hleft]

/-- The axial weighted version of the actual periodic lift belongs to unnormalized centered
cell L². -/
theorem memLp_axialHeatLift_cyl {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (f : X c m) :
    MemLp (fun z => axialWeight m z • xColumnHeatLift hc f z) 2 (Cyl.cellμ c) := by
  have hrad : MemLp (fun z => bracket z ^ m * (f : Plane → ℝ) z) 2
      (Cyl.cellμ c) := by
    rw [cylCell_eq_restrict_radial]
    exact (B0579.memLp_cellMeasure_iff c m).1 (Lp.memLp f)
  have hmeas : AEStronglyMeasurable
      (fun z => axialWeight m z • xColumnHeatLift hc f z) (Cyl.cellμ c) :=
    ((continuous_axialWeight m).aestronglyMeasurable.smul
      (stronglyMeasurable_xColumnHeatLift hc f).aestronglyMeasurable).mono_ac
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  refine ⟨hmeas, ?_⟩
  have hbound := eLpNorm_axialHeatLift_le_radialInput_cyl hc hm f
  exact lt_of_le_of_lt hbound hrad.eLpNorm_ne_top.lt_top

/-- The actual axial-weighted periodic lift as a normalized-cell Euclidean L² class. -/
noncomputable def axialWeightedHeatInput {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (f : X c m) : Lp Plane 2 (B0284.cellMeasure c) :=
  (HeatCylinder.memLp_cellMeasure_of_memLp_cyl hc
    ((continuous_axialWeight m).measurable.smul
      ((stronglyMeasurable_xColumnHeatLift hc f).measurable))
    (by
      intro z
      change axialWeight m (z.1 + c, z.2) • xColumnHeatLift hc f (z.1 + c, z.2) =
        axialWeight m z • xColumnHeatLift hc f z
      rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
        simp [axialWeight, axialBracket], periodic_xColumnHeatLift hc f z])
    (memLp_axialHeatLift_cyl hc hm f)).toLp
      (fun z => axialWeight m z • xColumnHeatLift hc f z)

/-- The normalized heat input retains the chosen actual periodic representative. -/
theorem coeFn_axialWeightedHeatInput {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (f : X c m) :
    (axialWeightedHeatInput hc hm f : Plane → Plane) =ᵐ[B0284.cellMeasure c]
      fun z => axialWeight m z • xColumnHeatLift hc f z := by
  exact (HeatCylinder.memLp_cellMeasure_of_memLp_cyl hc
    ((continuous_axialWeight m).measurable.smul
      ((stronglyMeasurable_xColumnHeatLift hc f).measurable))
    (by
      intro z
      change axialWeight m (z.1 + c, z.2) • xColumnHeatLift hc f (z.1 + c, z.2) =
        axialWeight m z • xColumnHeatLift hc f z
      rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
        simp [axialWeight, axialBracket], periodic_xColumnHeatLift hc f z])
    (memLp_axialHeatLift_cyl hc hm f)).coeFn_toLp

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.memLp_axialHeatLift_cyl
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.axialWeightedHeatInput
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.coeFn_axialWeightedHeatInput

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
