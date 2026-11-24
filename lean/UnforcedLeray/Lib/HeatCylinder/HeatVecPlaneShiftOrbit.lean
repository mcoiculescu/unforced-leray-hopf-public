import UnforcedLeray.Lib.HeatCylinder.HeatVecPlaneShiftGroup
import UnforcedLeray.Lib.HeatCylinder.CenteredHeatProjectionConditional
import UnforcedLeray.Units.B0284.Contraction

/-!
# Continuous planar translation orbits and Gaussian integrability

The actual centered-cell translation action is strongly continuous at every planar shift. This
makes its scalar Gaussian-weighted orbit Bochner integrable at positive heat age.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Cyl (L2v)
open UnforcedLeray.B0284 (heatKernel2)

/-- The planar translation orbit is continuous at every shift, by its group law and continuity
at zero on the actual centered-cell quotient. -/
theorem continuous_planeShiftL2_orbit {c : ℝ} (hc : 0 < c) (x : L2v c) :
    Continuous (fun w : Plane => planeShiftL2CLM hc w x) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  have hsubCont : Continuous (fun w : Plane => w - v) :=
    continuous_id.sub continuous_const
  have hsub : Tendsto (fun w : Plane => w - v) (𝓝 v) (𝓝 (0 : Plane)) := by
    simpa using hsubCont.tendsto v
  have hzero := (tendsto_planeShiftL2_centered hc (planeShiftL2 hc v x)).comp hsub
  have hfun : (fun w : Plane => planeShiftL2 hc w x) =
      fun w => planeShiftL2 hc (w - v) (planeShiftL2 hc v x) := by
    funext w
    rw [planeShiftL2_add_comp hc]
    congr 1
    ext <;> simp
  change Tendsto (fun w : Plane => planeShiftL2 hc w x) (𝓝 v)
    (𝓝 (planeShiftL2 hc v x))
  rw [hfun]
  exact hzero

/-- The actual positive-age Gaussian-weighted centered translation orbit is Bochner integrable.
The shifts are genuine centered-cell isometries, so the integrable majorant is exactly the heat
kernel times `‖x‖`. -/
theorem integrable_heatKernel2_smul_planeShiftL2CLM {c θ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (x : L2v c) :
    Integrable (fun w : Plane => heatKernel2 θ w • planeShiftL2CLM hc w x) := by
  have hcont := continuous_planeShiftL2_orbit hc x
  have hmeas : AEStronglyMeasurable
      (fun w : Plane => heatKernel2 θ w • planeShiftL2CLM hc w x) volume := by
    exact (UnforcedLeray.B0284.measurable_heatKernel2_right θ).aestronglyMeasurable.smul
      hcont.stronglyMeasurable.aestronglyMeasurable
  apply (integrable_norm_iff hmeas).1
  have hk := UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hnormshift : ∀ w : Plane, ‖planeShiftL2CLM hc w x‖ = ‖x‖ := by
    intro w
    change ‖UnforcedLeray.TrainB.qShiftL2Isometry hc (-w.1)
      (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x)‖ = ‖x‖
    rw [(UnforcedLeray.TrainB.qShiftL2Isometry hc (-w.1)).norm_map,
      (UnforcedLeray.TrainB.etaShiftL2 c (-w.2)).norm_map]
  have hnorm : (fun w : Plane =>
      ‖heatKernel2 θ w • planeShiftL2CLM hc w x‖) =
      fun w => heatKernel2 θ w * ‖x‖ := by
    funext w
    rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w),
      hnormshift w]
  rw [hnorm]
  exact hk.mul_const ‖x‖

#print axioms UnforcedLeray.HeatCylinder.continuous_planeShiftL2_orbit
#print axioms UnforcedLeray.HeatCylinder.integrable_heatKernel2_smul_planeShiftL2CLM

end UnforcedLeray.HeatCylinder
