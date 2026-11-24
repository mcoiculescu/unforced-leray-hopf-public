import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedCurlCurlIdentity
import UnforcedLeray.Lib.CZL2.TestProjection
import UnforcedLeray.Lib.PhaseSpace.Test

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint UnforcedLeray.RieszLp UnforcedLeray.PressureAnalysis
  UnforcedLeray.PhaseSpace

/-- Each component of the actual joint Newton vector potential agrees on a fixed phase slice
with the established scalar Newton convolution of that component of the original test. -/
theorem projectedTestNewtonVectorPotential_component {P : ℝ}
    {Φ : SpaceTime → Space} (hΦ : IsPhaseTest P Φ) (τ : ℝ) (y : Space)
    (i : Fin 3) :
    projectedTestNewtonVectorPotential Φ (τ, y) i =
      newtonConv (fun x : Space => Φ (τ, x) i) y := by
  unfold projectedTestNewtonVectorPotential
  rw [sum_smul_coordinateVector_apply]
  have hslice : (fun x : Space => (Φ ((τ, y) - (0, x))) i) =
      (fun x : Space => Φ (τ, y - x) i) := by
    funext x
    have hx : (τ, y) - (0, x) = (τ, y - x) := by ext <;> simp
    rw [hx]
  have hint : (∫ x : Space, newtonPotential x * (Φ ((τ, y) - (0, x))) i) =
      ∫ x : Space, newtonPotential x * Φ (τ, y - x) i := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [congrFun hslice x]
  rw [hint]
  simpa [newtonConv, sub_sub_cancel] using
    (integral_sub_left_eq_self
      (fun t : Space => newtonPotential (y - t) * Φ (τ, t) i) volume y)

#print axioms projectedTestNewtonVectorPotential_component

end UnforcedLeray.Cons.C03.Concrete

end
