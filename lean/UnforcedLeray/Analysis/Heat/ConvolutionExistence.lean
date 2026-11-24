import UnforcedLeray.Statement
import Mathlib.Analysis.Convolution
import Mathlib.Tactic

/-!
# Existence of the actual L¹–L² convolution

For an integrable scalar kernel and a square-integrable vector field on R³,
the Bochner convolution integrand is integrable at almost every output point.
The proof uses Tonelli on the integrable scalar convolution of the absolute
kernel with the squared field norm, then the elementary majorant r ≤ 1+r².
It does not use the totalized integral to bypass the convergence obligation.
-/

noncomputable section
open MeasureTheory
namespace UnforcedLeray.Heat

/-- The scalar-kernel/vector-field convolution genuinely converges almost everywhere. -/
theorem ae_integrable_convolution {k : Space → ℝ} {f : SpatialField}
    (hk : Integrable k volume) (hf : MemLp f 2 volume) :
    ∀ᵐ x ∂(volume : Measure Space),
      Integrable (fun y : Space => k y • f (x - y)) volume := by
  have hsq : Integrable (fun y : Space => ‖f y‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hconv := hk.norm.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hsq
  filter_upwards [hconv] with x hx
  have hq : Integrable (fun y : Space => ‖k y‖ * ‖f (x - y)‖ ^ 2) volume := hx
  have hm : AEStronglyMeasurable (fun y : Space => k y • f (x - y)) volume :=
    hk.aestronglyMeasurable.convolution_integrand_snd
      (ContinuousLinearMap.lsmul ℝ ℝ) hf.aestronglyMeasurable x
  apply (hk.norm.fun_add hq).mono' hm
  filter_upwards [] with y
  change ‖k y • f (x - y)‖ ≤ ‖k y‖ + ‖k y‖ * ‖f (x - y)‖ ^ 2
  rw [norm_smul]
  have hb : ‖f (x - y)‖ ≤ 1 + ‖f (x - y)‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f (x - y)‖ - 1 / 2)]
  calc
    ‖k y‖ * ‖f (x - y)‖ ≤ ‖k y‖ * (1 + ‖f (x - y)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ‖k y‖ + ‖k y‖ * ‖f (x - y)‖ ^ 2 := by ring

end UnforcedLeray.Heat
