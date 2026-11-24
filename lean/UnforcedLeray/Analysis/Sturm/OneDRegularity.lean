import UnforcedLeray.Analysis.Sturm.OneDRegularityKernel
import UnforcedLeray.Analysis.Sturm.OneDRegularityLocalKernel
import UnforcedLeray.Analysis.Sturm.OneDRegularityRepresentative
import UnforcedLeray.Analysis.Sturm.FreeResolventWeak

/-!
# Actual C¹ representatives for the one-dimensional free Green operator

The exponential kernel and its first derivative are L². Their convolution
with any L² datum is absolutely integrable pointwise. Local weighted
Lipschitz bounds justify differentiating the actual integral; L² translation
continuity makes the derivative continuous. A density/subsequence argument
identifies these classical functions with the previously constructed L²
operator and its derivative.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace UnforcedLeray.Sturm
open NonUniqueEuler.Sob NonUniqueEuler.Sob.EnergyAux

/-- Absolute integrability of the actual Green integrand for every L² datum. -/
theorem integrable_k0_mul_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (x : ℝ) :
    Integrable (fun y => (k0 L (x - y) : ℂ) * f y) :=
  (memLp_k0_shift_complex hL x).integrable_mul hf

theorem integrable_k1_mul_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (x : ℝ) :
    Integrable (fun y => (k1 L (x - y) : ℂ) * f y) :=
  (memLp_k1_shift_complex hL x).integrable_mul hf

/-- The actual all-L² kernel convolution has the claimed classical derivative. -/
theorem hasDerivAt_psi0_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (x₀ : ℝ) :
    HasDerivAt (psi0 L f) (-L * psi1 L f x₀) x₀ := by
  have hmeas : ∀ x, AEStronglyMeasurable (fun y => (k0 L (x - y) : ℂ) * f y) :=
    fun x => (integrable_k0_mul_of_memLp hL hf x).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable (fun y => ((-L * k1 L (x₀ - y) : ℝ) : ℂ) * f y) := by
    refine AEStronglyMeasurable.mul ?_ hf.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp (measurable_const.mul
      ((measurable_k1 L).comp (measurable_const.sub measurable_id)))).aestronglyMeasurable
  have hbound : Integrable (fun y => L * Real.exp L * k0 L (x₀ - y) * ‖f y‖) := by
    have h := ((memLp_k0_shift_real hL x₀).integrable_mul hf.norm).const_mul (L * Real.exp L)
    simpa only [Pi.mul_apply, mul_assoc] using h
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (x₀ := x₀)
    (s := Metric.ball x₀ 1)
    (F := fun x y => (k0 L (x - y) : ℂ) * f y)
    (F' := fun y => ((-L * k1 L (x₀ - y) : ℝ) : ℂ) * f y)
    (bound := fun y => L * Real.exp L * k0 L (x₀ - y) * ‖f y‖)
    (Metric.ball_mem_nhds x₀ (by norm_num)) (Eventually.of_forall hmeas)
    (integrable_k0_mul_of_memLp hL hf x₀) hF'm
    (Eventually.of_forall fun y => by
      refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_
      have hx0 : |x - x₀| ≤ 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hx.le
      have hx'0 : |x' - x₀| ≤ 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hx'.le
      have hb0 : 0 ≤ L * Real.exp L * k0 L (x₀ - y) * ‖f y‖ :=
        mul_nonneg (mul_nonneg (mul_nonneg hL.le (Real.exp_pos _).le)
          (k0_pos _ _).le) (norm_nonneg _)
      rw [dist_eq_norm, dist_eq_norm, ← sub_mul, norm_mul, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, Real.coe_nnabs, abs_of_nonneg hb0]
      have h := k0_local_lipschitz hL.le x x' x₀ y hx0 hx'0
      calc |k0 L (x - y) - k0 L (x' - y)| * ‖f y‖ ≤
          (L * Real.exp L * k0 L (x₀ - y) * |x - x'|) * ‖f y‖ :=
            mul_le_mul_of_nonneg_right h (norm_nonneg _)
        _ = L * Real.exp L * k0 L (x₀ - y) * ‖f y‖ * ‖x - x'‖ := by
          rw [Real.norm_eq_abs]
          ring)
    hbound
    (by
      filter_upwards [ae_ne_pt x₀] with y hy
      have hz : x₀ - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
      exact (HasDerivAt.comp_sub_const x₀ y (hasDerivAt_k0 L hz)).ofReal_comp.mul_const (f y))
  refine key.2.congr_deriv ?_
  unfold psi1
  rw [← integral_const_mul]
  congr 1
  funext y
  push_cast
  ring

theorem hasDerivAt_freeResolvent_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (x : ℝ) :
    HasDerivAt (freeResolvent L f) (freeResolventDeriv L f x) x := by
  have h := (hasDerivAt_psi0_of_memLp hL hf x).const_mul ((((2 * L)⁻¹ : ℝ) : ℂ))
  refine h.congr_deriv ?_
  unfold freeResolventDeriv
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  push_cast
  field_simp

theorem continuous_freeResolventDeriv_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) : Continuous (freeResolventDeriv L f) :=
  (continuous_psi1_of_memLp hL hf).const_mul _

theorem deriv_freeResolvent_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) : deriv (freeResolvent L f) = freeResolventDeriv L f := by
  funext x
  exact (hasDerivAt_freeResolvent_of_memLp hL hf x).deriv

theorem contDiff_one_freeResolvent_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) : ContDiff ℝ 1 (freeResolvent L f) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_freeResolvent_of_memLp hL hf x).differentiableAt, ?_⟩
  rw [deriv_freeResolvent_of_memLp hL hf]
  exact continuous_freeResolventDeriv_of_memLp hL hf

/-- Point evaluation of the explicit Green integral is a bounded L² functional. -/
def freeResolventEvaluation {L : ℝ} (hL : 0 < L) (x : ℝ) : ComplexL2 →L[ℂ] ℂ :=
  ((((2 * L)⁻¹ : ℝ) : ℂ)) •
    l2Pairing (fun y => (k0 L (x - y) : ℂ)) (memLp_k0_shift_complex hL x)

theorem freeResolventEvaluation_apply {L : ℝ} (hL : 0 < L) (x : ℝ) (f : ComplexL2) :
    freeResolventEvaluation hL x f = freeResolvent L (f : ℝ → ℂ) x := by
  simp only [freeResolventEvaluation, smul_apply, smul_eq_mul,
    l2Pairing_apply, freeResolvent, psi0]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun y => mul_comm _ _

def freeResolventDerivativeEvaluation {L : ℝ} (hL : 0 < L) (x : ℝ) : ComplexL2 →L[ℂ] ℂ :=
  (-(1 / 2 : ℂ)) •
    l2Pairing (fun y => (k1 L (x - y) : ℂ)) (memLp_k1_shift_complex hL x)

theorem freeResolventDerivativeEvaluation_apply {L : ℝ} (hL : 0 < L)
    (x : ℝ) (f : ComplexL2) :
    freeResolventDerivativeEvaluation hL x f = freeResolventDeriv L (f : ℝ → ℂ) x := by
  simp only [freeResolventDerivativeEvaluation, smul_apply, smul_eq_mul,
    l2Pairing_apply, freeResolventDeriv, psi1]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun y => mul_comm _ _

/-- Identification of the continuous Green representative for every L² datum. -/
theorem coeFn_freeResolventOperator {L : ℝ} (hL : 0 < L) (f : ComplexL2) :
    freeResolventOperator hL f =ᵐ[volume] freeResolvent L (f : ℝ → ℂ) := by
  apply ae_eq_pointwiseFormula_of_compact (freeResolventOperator hL)
    (fun g x => freeResolvent L (g : ℝ → ℂ) x) ?_
    (coeFn_freeResolventOperator_on_compact hL) f
  intro x
  convert (freeResolventEvaluation hL x).continuous using 1
  funext g
  exact (freeResolventEvaluation_apply hL x g).symm

theorem coeFn_freeResolventDerivativeOperator {L : ℝ} (hL : 0 < L) (f : ComplexL2) :
    freeResolventDerivativeOperator hL f =ᵐ[volume] freeResolventDeriv L (f : ℝ → ℂ) := by
  apply ae_eq_pointwiseFormula_of_compact (freeResolventDerivativeOperator hL)
    (fun g x => freeResolventDeriv L (g : ℝ → ℂ) x) ?_
    (coeFn_freeResolventDerivativeOperator_on_compact hL) f
  intro x
  convert (freeResolventDerivativeEvaluation hL x).continuous using 1
  funext g
  exact (freeResolventDerivativeEvaluation_apply hL x g).symm

end UnforcedLeray.Sturm
