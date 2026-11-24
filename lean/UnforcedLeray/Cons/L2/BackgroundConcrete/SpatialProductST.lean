import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProduct

/-! Lift the phasewise product derivative to the spacetime direction used in the weak equation. -/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace

/-- The scalar product with a bounded background has the expected line derivative along each
spatial spacetime direction. No derivative in the phase variable is used. -/
theorem hasLineDerivAt_scalarTestBackground_spaceTime {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    (τ : ℝ) (y v : Space) :
    HasLineDerivAt ℝ (fun z : SpaceTime => scalarTestBackground Φ U z)
      (fderiv ℝ (fun x : Space => scalarTestBackground Φ U (τ, x)) y v)
      (τ, y) (0, v) := by
  have h := hasLineDerivAt_scalarTestBackground hΦ hU τ y v
  simpa [HasLineDerivAt, scalarTestBackground] using h

#print axioms hasLineDerivAt_scalarTestBackground_spaceTime

end UnforcedLeray.Cons.C03.Concrete
