import UnforcedLeray.Analysis.Heat.ConvolutionL2
import UnforcedLeray.Analysis.WeakDerivative
import UnforcedLeray.Analysis.SobolevGraph.Graph
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Weak differentiation of actual L¹-kernel convolution

For a C¹ scalar kernel whose value and coordinate derivative belong to L¹,
the ordinary convolution with any vector L² field has the expected weak
coordinate derivative. The proof first uses classical differentiation and
integration by parts on compact smooth inputs, then passes through the proved
closed weak derivative graph using the density of compact smooth fields in L².
No differentiability or Sobolev regularity of the L² input is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff
namespace UnforcedLeray.Heat

/-- Derivative of the reflected translate used by convolution. -/
theorem fderiv_reflected_translate (f : SpatialField) (hf : Differentiable ℝ f)
    (x y a : Space) :
    fderiv ℝ (fun z : Space => f (x-z)) y a = -(fderiv ℝ f (x-y) a) := by
  have h := (hf (x-y)).hasFDerivAt.comp y ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  change HasFDerivAt (fun z : Space => f (x-z)) _ y at h
  rw [h.fderiv]
  simp

/-- Classical derivative of a convolution with a compact C¹ input. -/
theorem fderiv_convolution_compact (k : Space → ℝ) (hk : Integrable k volume)
    (f : SpatialField) (hfc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (a x : Space) :
    fderiv ℝ (convolution k f) x a =
      convolution k (fun y => fderiv ℝ f y a) x := by
  have h := hfc.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hk.locallyIntegrable hf x
  change HasFDerivAt (convolution k f) _ x at h
  rw [h.fderiv]
  exact MeasureTheory.convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ)
    hk.locallyIntegrable (hfc.fderiv ℝ) (hf.continuous_fderiv (by norm_num)) x a

/-- Integration by parts moves the derivative to the kernel, with convergent integrals. -/
theorem convolution_derivative_compact (k : Space → ℝ) (hk : ContDiff ℝ 1 k)
    (f : SpatialField) (hfc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (a x : Space) :
    convolution k (fun y => fderiv ℝ f y a) x =
      convolution (fun y => fderiv ℝ k y a) f x := by
  let q : SpatialField := fun y => f (x-y)
  have hqc : HasCompactSupport q := hfc.comp_homeomorph (Homeomorph.subLeft x)
  have hq : ContDiff ℝ 1 q := hf.comp (contDiff_const.sub contDiff_id)
  have hdq : Continuous (fun y => fderiv ℝ q y a) :=
    (hq.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdk : Continuous (fun y => fderiv ℝ k y a) :=
    (hk.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h1 : Integrable (fun y => fderiv ℝ k y a • q y) :=
    (hdk.smul hq.continuous).integrable_of_hasCompactSupport hqc.smul_left
  have h2 : Integrable (fun y => k y • fderiv ℝ q y a) :=
    (hk.continuous.smul hdq).integrable_of_hasCompactSupport
      (hqc.fderiv_apply ℝ a).smul_left
  have h0 : Integrable (fun y => k y • q y) :=
    (hk.continuous.smul hq.continuous).integrable_of_hasCompactSupport hqc.smul_left
  have hi := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h1 h2 h0
    (fun _ _ => (hk.differentiable (by norm_num)).differentiableAt)
    (fun _ _ => (hq.differentiable (by norm_num)).differentiableAt)
  have he : ∀ y, fderiv ℝ q y a = -(fderiv ℝ f (x-y) a) :=
    fun y => fderiv_reflected_translate f (hf.differentiable (by norm_num)) x y a
  simp only [he, smul_neg, integral_neg] at hi
  exact neg_injective hi

/-- The genuine weak derivative identity on compact C¹ inputs. -/
theorem hasWeakSpatialDerivative_convolution_compact
    (k : Space → ℝ) (hk : ContDiff ℝ 1 k) (hki : Integrable k volume)
    (f : SpatialField) (hfc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (i : Fin 3) :
    HasWeakSpatialDerivative i (convolution k f)
      (convolution (fun y => fderiv ℝ k y (coordinateVector i)) f) := by
  have hc : ContDiff ℝ 1 (convolution k f) :=
    hfc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hki.locallyIntegrable hf
  have h := hasWeakSpatialDerivative_of_contDiff hc i
  convert h using 1
  funext x
  rw [fderiv_convolution_compact k hki f hfc hf,
    convolution_derivative_compact k hk f hfc hf]

/-- Kernel convolution and its derivative convolution satisfy the actual closed
weak-derivative graph on every L² input. -/
theorem hasWeakSpatialDerivative_convolution_operator
    (k : Space → ℝ) (hk : ContDiff ℝ 1 k) (hki : Integrable k volume)
    (i : Fin 3) (hdi : Integrable (fun y => fderiv ℝ k y (coordinateVector i)) volume)
    (F : L2Space) :
    HasWeakSpatialDerivative i
      (convolutionOperator k hki F : SpatialField)
      (convolutionOperator (fun y => fderiv ℝ k y (coordinateVector i)) hdi F : SpatialField) := by
  let dk : Space → ℝ := fun y => fderiv ℝ k y (coordinateVector i)
  let A : L2Space →L[ℝ] L2Space := convolutionOperator k hki
  let B : L2Space →L[ℝ] L2Space := convolutionOperator dk hdi
  let S : Set L2Space := {F | HasWeakSpatialDerivative i (A F : SpatialField) (B F : SpatialField)}
  have hclosed : IsClosed S :=
    (SobolevGraph.isClosed_setOf_hasWeakSpatialDerivative i).preimage
      (A.continuous.prodMk B.continuous)
  have hdense : Dense {F : L2Space | ∃ g : SpatialField,
      (F : SpatialField) =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hsubset : {F : L2Space | ∃ g : SpatialField,
      (F : SpatialField) =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} ⊆ S := by
    rintro F ⟨g, hFg, hgc, hgs⟩
    have hraw := hasWeakSpatialDerivative_convolution_compact k hk hki g hgc
      (hgs.of_le (by simp)) i
    have hA : (A F : SpatialField) =ᵐ[volume] convolution k g :=
      (convolutionToL2_rep k hki F).trans (Eventually.of_forall fun x =>
        congrFun (convolution_congr_ae (EventuallyEq.rfl (f := k)) hFg) x)
    have hB : (B F : SpatialField) =ᵐ[volume] convolution dk g :=
      (convolutionToL2_rep dk hdi F).trans (Eventually.of_forall fun x =>
        congrFun (convolution_congr_ae (EventuallyEq.rfl (f := dk)) hFg) x)
    exact hraw.congr hA.symm hB.symm
  exact (closure_minimal hsubset hclosed) (hdense F)

/-- Weak derivative transport for the literal convolution of any L² field.
Both derivative and value are the genuine Bochner convolution functions. -/
theorem hasWeakSpatialDerivative_convolution
    (k : Space → ℝ) (hk : ContDiff ℝ 1 k) (hki : Integrable k volume)
    (i : Fin 3) (hdi : Integrable (fun y => fderiv ℝ k y (coordinateVector i)) volume)
    (f : SpatialField) (hf : MemLp f 2 volume) :
    HasWeakSpatialDerivative i (convolution k f)
      (convolution (fun y => fderiv ℝ k y (coordinateVector i)) f) := by
  let F : L2Space := hf.toLp f
  let dk : Space → ℝ := fun y => fderiv ℝ k y (coordinateVector i)
  have hraw := hasWeakSpatialDerivative_convolution_operator k hk hki i hdi F
  have hA : (convolutionOperator k hki F : SpatialField) =ᵐ[volume] convolution k f :=
    (convolutionToL2_rep k hki F).trans (Eventually.of_forall fun x =>
      congrFun (convolution_congr_ae (EventuallyEq.rfl (f := k)) hf.coeFn_toLp) x)
  have hB : (convolutionOperator dk hdi F : SpatialField) =ᵐ[volume] convolution dk f :=
    (convolutionToL2_rep dk hdi F).trans (Eventually.of_forall fun x =>
      congrFun (convolution_congr_ae (EventuallyEq.rfl (f := dk)) hf.coeFn_toLp) x)
  exact hraw.congr hA hB

end UnforcedLeray.Heat

