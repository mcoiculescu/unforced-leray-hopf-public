import UnforcedLeray.Analysis.Heat.KernelSemigroup
import UnforcedLeray.Analysis.Heat.Averaging
import UnforcedLeray.Analysis.Heat.ConvolutionL2

/-!
# The actual heat semigroup on L²(R³)

Pointwise heat integrability and the Gaussian kernel identity justify
associating the literal Bochner integrals. The resulting identity is then
transferred to the standard L² quotient operators.
-/
noncomputable section
open MeasureTheory Filter
open scoped Convolution
namespace UnforcedLeray.Heat
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Heat averages are genuinely a.e. strongly measurable. -/
theorem average_aestronglyMeasurable (t : ℝ) {f : Space → V}
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (average t f) volume := by
  have hk : AEStronglyMeasurable (kernel t) volume :=
    (Gaussian.kernel_smooth (4*t)).continuous.aestronglyMeasurable
  exact (hk.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hf).integral_prod_right'

variable [CompleteSpace V]

omit [NormedSpace ℝ V] [CompleteSpace V] in
/-- The nested nonnegative norm convolution converges, by the exact L²-to-uniform bound. -/
theorem norm_average_outer_integrable {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {f : Space → V} (hf : MemLp f 2 volume) (x : Space) :
    Integrable (fun y : Space => kernel s y * average t (fun z => ‖f z‖) (x-y)) := by
  let C : ℝ := (8 * Real.pi * t) ^ (-(3 : ℝ) / 4) *
    (eLpNorm (fun z => ‖f z‖) 2 volume).toReal
  have hm := (average_aestronglyMeasurable t hf.norm.aestronglyMeasurable).comp_quasiMeasurePreserving
    (Measure.measurePreserving_sub_left (volume : Measure Space) x).quasiMeasurePreserving
  apply ((kernel_integrable hs).mul_const C).mono'
    ((kernel_integrable hs).aestronglyMeasurable.mul hm)
  filter_upwards [] with y
  change ‖kernel s y * average t (fun z => ‖f z‖) (x-y)‖ ≤ kernel s y * C
  rw [norm_mul, Real.norm_of_nonneg (kernel_nonneg hs y)]
  exact mul_le_mul_of_nonneg_left
    (average_norm_le_L2 ht (fun z => ‖f z‖) hf.norm (x-y)) (kernel_nonneg hs y)

/-- Positive-time addition law for the literal heat integral at every spatial point. -/
theorem average_add_time {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {f : Space → V} (hf : MemLp f 2 volume) :
    average (s+t) f = average s (average t f) := by
  let MM : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  let SM : ℝ →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.lsmul ℝ ℝ
  have hks : (fun y => ‖kernel s y‖) = kernel s := by
    funext y
    exact Real.norm_of_nonneg (kernel_nonneg hs y)
  have hkt : (fun y => ‖kernel t y‖) = kernel t := by
    funext y
    exact Real.norm_of_nonneg (kernel_nonneg ht y)
  have hfg : ∀ᵐ y : Space, ConvolutionExistsAt (kernel s) (kernel t) y MM volume :=
    Eventually.of_forall (fun y => kernel_product_integrable hs ht y)
  have hgk : ∀ᵐ y : Space,
      ConvolutionExistsAt (fun z => ‖kernel t z‖) (fun z => ‖f z‖) y MM volume := by
    rw [hkt]
    exact Eventually.of_forall (fun y => average_integrable ht hf.norm y)
  have hkconv : (kernel s ⋆[MM] kernel t) = kernel (s+t) :=
    funext (fun x => integral_kernel_product hs ht x)
  funext x
  have hfgk : ConvolutionExistsAt (fun z => ‖kernel s z‖)
      ((fun z => ‖kernel t z‖) ⋆[MM] (fun z => ‖f z‖)) x MM volume := by
    rw [hks, hkt]
    exact norm_average_outer_integrable hs ht hf x
  have ha := MeasureTheory.convolution_assoc MM SM SM SM
    (fun a b v => mul_smul a b v)
    (kernel_integrable hs).aestronglyMeasurable
    (kernel_integrable ht).aestronglyMeasurable hf.aestronglyMeasurable hfg hgk hfgk
  rw [hkconv] at ha
  exact ha

/-- The bounded operators induced by the actual heat kernels satisfy the semigroup law. -/
theorem convolutionOperator_heat_add_time {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    convolutionOperator (kernel (s+t)) (kernel_integrable (add_pos hs ht)) =
      (convolutionOperator (kernel s) (kernel_integrable hs)).comp
        (convolutionOperator (kernel t) (kernel_integrable ht)) := by
  apply ContinuousLinearMap.ext
  intro f
  change convolutionToL2 (kernel (s+t)) (kernel_integrable (add_pos hs ht)) f =
    convolutionToL2 (kernel s) (kernel_integrable hs)
      (convolutionToL2 (kernel t) (kernel_integrable ht) f)
  apply Lp.ext
  have hc := convolution_congr_ae (Filter.EventuallyEq.rfl (f := kernel s))
    (convolutionToL2_rep (kernel t) (kernel_integrable ht) f)
  filter_upwards [convolutionToL2_rep (kernel (s+t)) (kernel_integrable (add_pos hs ht)) f,
    convolutionToL2_rep (kernel s) (kernel_integrable hs)
      (convolutionToL2 (kernel t) (kernel_integrable ht) f)] with x h1 h2
  rw [h1, h2, hc]
  exact congrFun (average_add_time hs ht (Lp.memLp f)) x

end UnforcedLeray.Heat
