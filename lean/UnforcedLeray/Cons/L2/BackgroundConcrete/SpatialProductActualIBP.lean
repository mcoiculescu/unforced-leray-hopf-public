import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductPairings
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductIBP

/-! The spatial line-IBP identity with all actual compact-test integrability clauses discharged. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace

/-- Spatial integration by parts for the actual scalar product `Φ·U`, with all three integrability
clauses proved from the actual bounded-background hypotheses. -/
theorem integral_spatialIBP_scalarTestBackground {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {η : SpaceTime → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (j : Fin 3) :
    ∫ z : SpaceTime, η z •
        fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
          (EuclideanSpace.single j (1 : ℝ)) ∂volume =
      -∫ z : SpaceTime,
        fderiv ℝ η z (0, EuclideanSpace.single j (1 : ℝ)) •
          scalarTestBackground Φ U z ∂volume := by
  obtain ⟨h1, h2, h3⟩ := scalarTestBackground_linePairings_integrable hΦ hU hη hηc j
  exact integral_smul_fderiv_scalarTestBackground_eq_neg hΦ hU hη
    (EuclideanSpace.single j (1 : ℝ)) h1 h2 h3

#print axioms integral_spatialIBP_scalarTestBackground

end UnforcedLeray.Cons.C03.Concrete
