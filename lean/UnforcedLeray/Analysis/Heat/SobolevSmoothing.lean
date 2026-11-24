import UnforcedLeray.Analysis.Heat.ConvolutionWeakDerivative
import UnforcedLeray.Analysis.Heat.KernelNorm
import UnforcedLeray.Analysis.Heat.Derivatives
import UnforcedLeray.Analysis.SobolevGraph.H2Functions

/-!
# Actual H¹ and H² heat smoothing on R³

The spatial derivative kernels are the derivatives of the viscosity-one heat
kernel. Their L¹ integrability and the genuine convolution differentiation
theorem give weak derivatives for every L² input. The resulting operators take
values in the complete weak Sobolev Hilbert graphs, with no regularity assumption
on the input and no asserted abstract smoothing operator.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace UnforcedLeray.Heat

/-- The actual i-th spatial derivative of the standard heat kernel. -/
def firstDerivativeKernel (t : ℝ) (i : Fin 3) : Space → ℝ :=
  Gaussian.firstKernel (4*t) (coordinateVector i)

/-- The actual ordered (i,j) spatial second derivative of the heat kernel. -/
def secondDerivativeKernel (t : ℝ) (i j : Fin 3) : Space → ℝ :=
  Gaussian.secondKernel (4*t) (coordinateVector i) (coordinateVector j)

theorem kernel_fderiv_coordinate (t : ℝ) (i : Fin 3) (x : Space) :
    fderiv ℝ (kernel t) x (coordinateVector i) = firstDerivativeKernel t i x :=
  Gaussian.kernel_fderiv (4*t) (coordinateVector i) x

theorem firstDerivativeKernel_fderiv (t : ℝ) (i j : Fin 3) (x : Space) :
    fderiv ℝ (firstDerivativeKernel t i) x (coordinateVector j) =
      secondDerivativeKernel t i j x :=
  Gaussian.firstKernel_fderiv (4*t) (coordinateVector i) (coordinateVector j) x

theorem firstDerivativeKernel_smooth (t : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (firstDerivativeKernel t i) :=
  Gaussian.firstKernel_smooth (4*t) (coordinateVector i)

theorem secondDerivativeKernel_smooth (t : ℝ) (i j : Fin 3) :
    ContDiff ℝ ∞ (secondDerivativeKernel t i j) :=
  Gaussian.secondKernel_smooth (4*t) (coordinateVector i) (coordinateVector j)

theorem firstDerivativeKernel_integrable {t : ℝ} (ht : 0 < t) (i : Fin 3) :
    Integrable (firstDerivativeKernel t i) volume :=
  Gaussian.firstKernel_integrable (by positivity) (coordinateVector i)

theorem secondDerivativeKernel_integrable {t : ℝ} (ht : 0 < t) (i j : Fin 3) :
    Integrable (secondDerivativeKernel t i j) volume :=
  Gaussian.secondKernel_integrable (by positivity) (coordinateVector i) (coordinateVector j)

/-- First derivative convolution on the actual vector L² quotient. -/
def firstDerivativeOperator {t : ℝ} (ht : 0 < t) (i : Fin 3) : L2Space →L[ℝ] L2Space :=
  convolutionOperator (firstDerivativeKernel t i) (firstDerivativeKernel_integrable ht i)

/-- Second derivative convolution on the actual vector L² quotient. -/
def secondDerivativeOperator {t : ℝ} (ht : 0 < t) (i j : Fin 3) : L2Space →L[ℝ] L2Space :=
  convolutionOperator (secondDerivativeKernel t i j) (secondDerivativeKernel_integrable ht i j)

/-- The first derivative kernel gives the genuine weak derivative for every L² input. -/
theorem heat_hasWeakFirst {t : ℝ} (ht : 0 < t) (F : L2Space) (i : Fin 3) :
    HasWeakSpatialDerivative i
      (convolutionOperator (kernel t) (kernel_integrable ht) F : SpatialField)
      (firstDerivativeOperator ht i F : SpatialField) := by
  have hdi : Integrable (fun y => fderiv ℝ (kernel t) y (coordinateVector i)) volume := by
    simpa only [kernel_fderiv_coordinate] using firstDerivativeKernel_integrable ht i
  have h := hasWeakSpatialDerivative_convolution_operator (kernel t)
    ((Gaussian.kernel_smooth (4*t)).of_le (by simp)) (kernel_integrable ht) i hdi F
  simpa only [kernel_fderiv_coordinate, firstDerivativeOperator] using h

/-- The ordered second derivative kernels give the actual weak derivative of each first. -/
theorem heat_hasWeakSecond {t : ℝ} (ht : 0 < t) (F : L2Space) (i j : Fin 3) :
    HasWeakSpatialDerivative j
      (firstDerivativeOperator ht i F : SpatialField)
      (secondDerivativeOperator ht i j F : SpatialField) := by
  have hdi : Integrable
      (fun y => fderiv ℝ (firstDerivativeKernel t i) y (coordinateVector j)) volume := by
    simpa only [firstDerivativeKernel_fderiv] using secondDerivativeKernel_integrable ht i j
  have h := hasWeakSpatialDerivative_convolution_operator (firstDerivativeKernel t i)
    ((firstDerivativeKernel_smooth t i).of_le (by simp))
    (firstDerivativeKernel_integrable ht i) j hdi F
  simpa only [firstDerivativeKernel_fderiv, firstDerivativeOperator,
    secondDerivativeOperator] using h

/-- Heat smoothing into the complete weak H¹ graph. -/
def smoothedH1 {t : ℝ} (ht : 0 < t) (F : L2Space) : SobolevGraph.H1 :=
  SobolevGraph.H1.ofWeakDerivatives
    (convolutionOperator (kernel t) (kernel_integrable ht) F)
    (fun i => firstDerivativeOperator ht i F) (heat_hasWeakFirst ht F)

/-- Heat smoothing into the complete weak H² graph with ordered second derivatives. -/
def smoothedH2 {t : ℝ} (ht : 0 < t) (F : L2Space) : SobolevGraph.H2 :=
  SobolevGraph.H2.ofWeakDerivatives
    (convolutionOperator (kernel t) (kernel_integrable ht) F)
    (fun i => firstDerivativeOperator ht i F)
    (fun i j => secondDerivativeOperator ht i j F)
    (heat_hasWeakFirst ht F) (heat_hasWeakSecond ht F)

@[simp] theorem smoothedH1_value {t : ℝ} (ht : 0 < t) (F : L2Space) :
    (smoothedH1 ht F).value = convolutionOperator (kernel t) (kernel_integrable ht) F := rfl

@[simp] theorem smoothedH1_derivative {t : ℝ} (ht : 0 < t) (F : L2Space) (i : Fin 3) :
    (smoothedH1 ht F).derivative i = firstDerivativeOperator ht i F := rfl

@[simp] theorem smoothedH2_value {t : ℝ} (ht : 0 < t) (F : L2Space) :
    (smoothedH2 ht F).value = convolutionOperator (kernel t) (kernel_integrable ht) F := rfl

@[simp] theorem smoothedH2_first {t : ℝ} (ht : 0 < t) (F : L2Space) (i : Fin 3) :
    (smoothedH2 ht F).first i = firstDerivativeOperator ht i F := rfl

@[simp] theorem smoothedH2_second {t : ℝ} (ht : 0 < t) (F : L2Space) (i j : Fin 3) :
    (smoothedH2 ht F).second i j = secondDerivativeOperator ht i j F := rfl

/-- The heat-to-H¹ smoothing operator is genuinely linear and continuous. -/
def heatToH1 {t : ℝ} (ht : 0 < t) : L2Space →L[ℝ] SobolevGraph.H1 where
  toFun := smoothedH1 ht
  map_add' F G := by
    apply SobolevGraph.H1.ext
    change convolutionOperator (kernel t) (kernel_integrable ht) (F+G) = _
    exact map_add _ F G
  map_smul' c F := by
    apply SobolevGraph.H1.ext
    change convolutionOperator (kernel t) (kernel_integrable ht) (c • F) = _
    exact map_smul _ c F
  cont := by
    apply continuousOn_univ.mp
    apply (SobolevGraph.H1.continuousOn_iff_components (smoothedH1 ht) univ).mpr
    exact ⟨(convolutionOperator (kernel t) (kernel_integrable ht)).continuous.continuousOn,
      fun i => (firstDerivativeOperator ht i).continuous.continuousOn⟩

/-- The heat-to-H² smoothing operator is genuinely linear and continuous. -/
def heatToH2 {t : ℝ} (ht : 0 < t) : L2Space →L[ℝ] SobolevGraph.H2 where
  toFun := smoothedH2 ht
  map_add' F G := by
    apply SobolevGraph.H2.ext
    change convolutionOperator (kernel t) (kernel_integrable ht) (F+G) = _
    exact map_add _ F G
  map_smul' c F := by
    apply SobolevGraph.H2.ext
    change convolutionOperator (kernel t) (kernel_integrable ht) (c • F) = _
    exact map_smul _ c F
  cont := by
    apply continuousOn_univ.mp
    apply (SobolevGraph.H2.continuousOn_iff_components (smoothedH2 ht) univ).mpr
    exact ⟨(convolutionOperator (kernel t) (kernel_integrable ht)).continuous.continuousOn,
      (fun i => (firstDerivativeOperator ht i).continuous.continuousOn),
      fun i j => (secondDerivativeOperator ht i j).continuous.continuousOn⟩

@[simp] theorem heatToH1_value {t : ℝ} (ht : 0 < t) (F : L2Space) :
    (heatToH1 ht F).value = convolutionOperator (kernel t) (kernel_integrable ht) F := rfl

@[simp] theorem heatToH1_derivative {t : ℝ} (ht : 0 < t) (F : L2Space) (i : Fin 3) :
    (heatToH1 ht F).derivative i = firstDerivativeOperator ht i F := rfl

@[simp] theorem heatToH2_value {t : ℝ} (ht : 0 < t) (F : L2Space) :
    (heatToH2 ht F).value = convolutionOperator (kernel t) (kernel_integrable ht) F := rfl

@[simp] theorem heatToH2_first {t : ℝ} (ht : 0 < t) (F : L2Space) (i : Fin 3) :
    (heatToH2 ht F).first i = firstDerivativeOperator ht i F := rfl

@[simp] theorem heatToH2_second {t : ℝ} (ht : 0 < t) (F : L2Space) (i j : Fin 3) :
    (heatToH2 ht F).second i j = secondDerivativeOperator ht i j F := rfl

/-- The H² value is the literal heat convolution, up to the standard null-set quotient. -/
theorem heatToH2_rep {t : ℝ} (ht : 0 < t) (F : L2Space) :
    ((heatToH2 ht F).value : SpatialField) =ᵐ[volume] convolution (kernel t) F :=
  convolutionToL2_rep (kernel t) (kernel_integrable ht) F

end UnforcedLeray.Heat
