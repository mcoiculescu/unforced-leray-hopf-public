import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialSource
import UnforcedLeray.Lib.Kernels.ParamIntegral

set_option autoImplicit false

noncomputable section

open MeasureTheory
open Metric
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0412
open UnforcedLeray.RieszLp
open UnforcedLeray.PressureAnalysis

/-- Measurability of the actual Newton kernel used by the parameter integral. -/
theorem aestronglyMeasurable_newtonPotential : AEStronglyMeasurable newtonPotential volume := by
  exact newtonPotential_locallyIntegrable.aestronglyMeasurable

/-- The absolute Newton kernel is integrable on every compact spatial ball. -/
theorem integrable_newtonPotential_abs_on_closedBall (R : ℝ) :
    Integrable ((closedBall (0 : Space) R).indicator (fun x => |newtonPotential x|)) volume := by
  have hNabs : LocallyIntegrable (fun x => |newtonPotential x|) volume :=
    newtonPotential_locallyIntegrable.mono aestronglyMeasurable_newtonPotential.norm
      (Filter.Eventually.of_forall fun _ => by simp)
  apply (integrable_indicator_iff isClosed_closedBall.measurableSet).2
  exact hNabs.integrableOn_isCompact (isCompact_closedBall (0 : Space) R)

/-- All iterated phase/spatial derivatives of a shifted Newton-kernel integrand land on the
source; the singular Newton kernel is only a scalar factor. -/
theorem iteratedFDeriv_projectedPotentialReKernelIntegrand {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (x : Space) (n : ℕ) (p : ℝ × Space) :
    iteratedFDeriv ℝ n
      (fun z : ℝ × Space => newtonPotential x * projectedPotentialReDiv Φ (z.1, z.2 - x)) p =
      newtonPotential x • iteratedFDeriv ℝ n (projectedPotentialReDiv Φ) (p - (0, x)) := by
  have hshift' : ContDiff ℝ ∞
      (fun z : ℝ × Space => projectedPotentialReDiv Φ (z - (0, x))) := by
    exact (isPhaseTest_projectedPotentialReDiv hΦ).smooth.comp (by fun_prop)
  have hkernel : (fun z : ℝ × Space =>
      newtonPotential x * projectedPotentialReDiv Φ (z.1, z.2 - x)) =
      fun z => newtonPotential x • projectedPotentialReDiv Φ (z - (0, x)) := by
    funext z
    have hz : z - (0, x) = (z.1, z.2 - x) := by ext <;> simp
    rw [hz]
    simp [smul_eq_mul]
  rw [hkernel]
  change iteratedFDeriv ℝ n
      (fun z : ℝ × Space => newtonPotential x • projectedPotentialReDiv Φ (z - (0, x))) p = _
  rw [iteratedFDeriv_const_smul_apply' (hshift'.contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_comp_sub']

/-- Imaginary-source counterpart of the shifted Newton-kernel derivative formula. -/
theorem iteratedFDeriv_projectedPotentialImKernelIntegrand {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (x : Space) (n : ℕ) (p : ℝ × Space) :
    iteratedFDeriv ℝ n
      (fun z : ℝ × Space => newtonPotential x * projectedPotentialImDiv Φ (z.1, z.2 - x)) p =
      newtonPotential x • iteratedFDeriv ℝ n (projectedPotentialImDiv Φ) (p - (0, x)) := by
  have hshift' : ContDiff ℝ ∞
      (fun z : ℝ × Space => projectedPotentialImDiv Φ (z - (0, x))) := by
    exact (isPhaseTest_projectedPotentialImDiv hΦ).smooth.comp (by fun_prop)
  have hkernel : (fun z : ℝ × Space =>
      newtonPotential x * projectedPotentialImDiv Φ (z.1, z.2 - x)) =
      fun z => newtonPotential x • projectedPotentialImDiv Φ (z - (0, x)) := by
    funext z
    have hz : z - (0, x) = (z.1, z.2 - x) := by ext <;> simp
    rw [hz]
    simp [smul_eq_mul]
  rw [hkernel]
  change iteratedFDeriv ℝ n
      (fun z : ℝ × Space => newtonPotential x • projectedPotentialImDiv Φ (z - (0, x))) p = _
  rw [iteratedFDeriv_const_smul_apply' (hshift'.contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_comp_sub']

/-- The translated-source parameter integral for the real Newton correction. Derivatives in both
phase and space can be put on the compact smooth source, leaving the locally integrable Newton
kernel fixed in the integration variable. -/
def projectedPotentialReParamIntegral (Φ : ℝ × Space → CVec3) (p : ℝ × Space) : ℝ :=
  ∫ x, newtonPotential x * projectedPotentialReDiv Φ (p.1, p.2 - x)

/-- The translated-source parameter integral for the imaginary Newton correction. -/
def projectedPotentialImParamIntegral (Φ : ℝ × Space → CVec3) (p : ℝ × Space) : ℝ :=
  ∫ x, newtonPotential x * projectedPotentialImDiv Φ (p.1, p.2 - x)

/-- The real parameter integral is exactly the actual Newton convolution defining the projected
test correction, not a newly chosen representative. -/
theorem projectedPotentialRePath_eq_paramIntegral {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) (y : Space) :
    projectedPotentialRePath Φ (τ, y) = projectedPotentialReParamIntegral Φ (τ, y) := by
  change lerayPotential (projectedPotentialReTest Φ τ) y = _
  rw [lerayPotential, newtonConv_eq_convolution, convolution_def]
  unfold projectedPotentialReParamIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← projectedPotentialReDiv_slice Φ hΦ τ (y - x)]
  simp [ContinuousLinearMap.lsmul_apply]

/-- The imaginary parameter integral is exactly the actual Newton convolution defining the
projected test correction. -/
theorem projectedPotentialImPath_eq_paramIntegral {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) (y : Space) :
    projectedPotentialImPath Φ (τ, y) = projectedPotentialImParamIntegral Φ (τ, y) := by
  change lerayPotential (projectedPotentialImTest Φ τ) y = _
  rw [lerayPotential, newtonConv_eq_convolution, convolution_def]
  unfold projectedPotentialImParamIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← projectedPotentialImDiv_slice Φ hΦ τ (y - x)]
  simp [ContinuousLinearMap.lsmul_apply]

/-- For each fixed kernel point, the real integrand is jointly smooth in phase and space. -/
theorem contDiff_projectedPotentialReKernelIntegrand {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (x : Space) :
    ContDiff ℝ ∞ (fun p : ℝ × Space =>
      newtonPotential x * projectedPotentialReDiv Φ (p.1, p.2 - x)) := by
  have hshift : ContDiff ℝ ∞ (fun p : ℝ × Space => (p.1, p.2 - x)) := by fun_prop
  exact (contDiff_const.mul ((isPhaseTest_projectedPotentialReDiv hΦ).smooth.comp hshift))

/-- For each fixed kernel point, the imaginary integrand is jointly smooth in phase and space. -/
theorem contDiff_projectedPotentialImKernelIntegrand {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (x : Space) :
    ContDiff ℝ ∞ (fun p : ℝ × Space =>
      newtonPotential x * projectedPotentialImDiv Φ (p.1, p.2 - x)) := by
  have hshift : ContDiff ℝ ∞ (fun p : ℝ × Space => (p.1, p.2 - x)) := by fun_prop
  exact (contDiff_const.mul ((isPhaseTest_projectedPotentialImDiv hΦ).smooth.comp hshift))

#print axioms projectedPotentialRePath_eq_paramIntegral
#print axioms projectedPotentialImPath_eq_paramIntegral
#print axioms iteratedFDeriv_projectedPotentialReKernelIntegrand
#print axioms iteratedFDeriv_projectedPotentialImKernelIntegrand
#print axioms contDiff_projectedPotentialReKernelIntegrand
#print axioms contDiff_projectedPotentialImKernelIntegrand

end UnforcedLeray.Cons.C03.Concrete

end
