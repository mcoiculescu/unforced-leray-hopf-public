import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.AxialHeatIntertwining
import UnforcedLeray.Units.B0289.Semigroup

/-!
# Exact axial-weight heat commutator

For the actual periodic `X_m` lift, the difference between multiplying after heat and heating
the axially weighted field is an integral of the weight difference. The pointwise identity below
is stated at points where the two literal Gaussian integrals are finite; the preceding weighted
L² results supply that condition almost everywhere on the cylinder cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0579 hiding Plane

/-- The exact pointwise commutator formula for the literal B0284 heat convolution. -/
theorem axialHeatCommutator_identity {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) (f : X c m) {z : Plane}
    (hraw : B0284.heatAbs θ (xColumnHeatLift hc f) z ≠ ⊤)
    (hax : B0284.heatAbs θ
      (fun x => axialWeight m x • xColumnHeatLift hc f x) z ≠ ⊤) :
    axialWeight m z • B0284.heat θ (xColumnHeatLift hc f) z -
      B0284.heat θ (fun x => axialWeight m x • xColumnHeatLift hc f x) z =
      ∫ w : Plane, B0284.heatKernel2 θ w •
        ((axialWeight m z - axialWeight m (z - w)) • xColumnHeatLift hc f (z - w)) := by
  let g := xColumnHeatLift hc f
  let ag := fun x : Plane => axialWeight m x • g x
  have hg : AEStronglyMeasurable g volume :=
    (stronglyMeasurable_xColumnHeatLift hc f).aestronglyMeasurable
  have hag : AEStronglyMeasurable ag volume := by
    exact (continuous_axialWeight m).aestronglyMeasurable.smul hg
  have hiraw := B0289.integrable_heat_integrand hθ hg hraw
  have hiax := B0289.integrable_heat_integrand hθ hag hax
  have hiscale : Integrable (fun w : Plane =>
      axialWeight m z • (B0284.heatKernel2 θ w • g (z - w))) :=
    hiraw.smul_of_top_right (memLp_top_const (axialWeight m z))
  rw [B0284.heat_apply_of_pos hθ, B0284.heat_apply_of_pos hθ]
  change axialWeight m z • (∫ w : Plane, B0284.heatKernel2 θ w • g (z - w)) -
      ∫ w : Plane, B0284.heatKernel2 θ w • ag (z - w) = _
  calc
    axialWeight m z • (∫ w : Plane, B0284.heatKernel2 θ w • g (z - w)) -
        ∫ w : Plane, B0284.heatKernel2 θ w • ag (z - w) =
        (∫ w : Plane, axialWeight m z •
          (B0284.heatKernel2 θ w • g (z - w))) -
          ∫ w : Plane, B0284.heatKernel2 θ w • ag (z - w) := by
            rw [← integral_smul]
    _ = ∫ w : Plane, (axialWeight m z •
          (B0284.heatKernel2 θ w • g (z - w)) -
          B0284.heatKernel2 θ w • ag (z - w)) := (integral_sub hiscale hiax).symm
    _ = ∫ w : Plane, B0284.heatKernel2 θ w •
          ((axialWeight m z - axialWeight m (z - w)) • g (z - w)) := by
            congr 1
            funext w
            simp only [ag, smul_smul]
            have hcoeff : axialWeight m z * B0284.heatKernel2 θ w -
                B0284.heatKernel2 θ w * axialWeight m (z - w) =
                B0284.heatKernel2 θ w *
                  (axialWeight m z - axialWeight m (z - w)) := by ring
            rw [← sub_smul, hcoeff]

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.axialHeatCommutator_identity

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
