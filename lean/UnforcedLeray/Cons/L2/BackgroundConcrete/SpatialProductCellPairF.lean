import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellPairingLimit
import UnforcedLeray.Cons.L2.BackgroundConcrete.RepresentativeLp

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace

/-- The explicit normalized pairing over a phase cell is the product-measure integral on the
restricted spacetime cell, whenever its actual integrand is integrable there. -/
theorem pairF_eq_restrictedProductIntegral {P : ℝ} [Fact (0 < P)]
    {F G : SpaceTime → CVec3}
    (hInt : Integrable (fun z => dotL (F z) (G z))
      (volume.restrict (phaseCell P))) :
    pairF P F G = P⁻¹ •
      ∫ z, dotL (F z) (G z) ∂(volume.restrict (phaseCell P)) := by
  let μ : Measure ℝ := volume
  let ν : Measure Space := volume
  have hprod : (volume : Measure SpaceTime).restrict (phaseCell P) =
      (μ.restrict (Ioc (0 : ℝ) P)).prod ν := by
    simpa [μ, ν, phaseCell, Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Space)) (Ioc (0 : ℝ) P)).symm
  have hInt' : Integrable (fun z : ℝ × Space => dotL (F z) (G z))
      ((μ.restrict (Ioc (0 : ℝ) P)).prod ν) := by
    rw [← hprod]
    exact hInt
  have hiter :
      ∫ t in Ioc (0 : ℝ) P, ∫ y : Space, dotL (F (t, y)) (G (t, y)) =
        ∫ z, dotL (F z) (G z) ∂(volume.restrict (phaseCell P)) := by
    calc
      ∫ t in Ioc (0 : ℝ) P, ∫ y : Space, dotL (F (t, y)) (G (t, y)) =
          ∫ t, ∫ y, dotL (F (t, y)) (G (t, y)) ∂ν ∂(μ.restrict (Ioc 0 P)) := by
            rfl
      _ = ∫ z, dotL (F z) (G z) ∂((μ.restrict (Ioc 0 P)).prod ν) :=
        (integral_prod _ hInt').symm
      _ = ∫ z, dotL (F z) (G z) ∂(volume.restrict (phaseCell P)) := by
        rw [hprod]
  unfold pairF phaseInt
  rw [hiter]

#print axioms pairF_eq_restrictedProductIntegral

end UnforcedLeray.Cons.C03.Concrete
