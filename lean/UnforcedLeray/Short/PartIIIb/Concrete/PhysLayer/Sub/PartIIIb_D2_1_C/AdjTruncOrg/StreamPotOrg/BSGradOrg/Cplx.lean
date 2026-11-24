import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.BSGradOrg.Basic
import UnforcedLeray.Analysis.LerayProjection.TranslationTests

/-!
# `BSGrad` ingredients: the complex scalar identities

Source `the November 2 reference manuscript` lines 1351-1362.

* `bsgKernelCplx`: `∫ K_c(y - z) ∂ⱼθ(y) dy = T_{cj} θ(z)` for complex compact smooth `θ`
  (real and imaginary parts, `bsgKernelReal`);
* `bsgDualCplx`: `∫ θ R_{jc} g = ∫ T_{cj} θ g` for complex compact smooth `θ` and `g ∈ L²(ℝ³; ℂ)`
  (four real pairings, `bsgDualReal`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

/-- The real kernel `K_c(y - z)` times a real test is integrable. -/
theorem bsg_integrable_kernel (c : Fin 3) (z : Space) {g : Space → ℝ} (hg : IsSpatialTest g) :
    Integrable (fun y : Space => (4 * Real.pi)⁻¹ * (‖y - z‖ ^ 3)⁻¹ * (y - z) c * g y) := by
  have ht := UnforcedLeray.Leray.isSpatialTest_translate z hg
  have h := (UnforcedLeray.PressureAnalysis.newtonGradientKernel_integrable_mul_test c
    ht.continuous ht.compact).comp_sub_right z
  refine h.neg.congr (Eventually.of_forall fun y => ?_)
  simp only [sub_add_cancel, UnforcedLeray.PressureAnalysis.newtonGradientKernel, Pi.neg_apply]
  ring

/-- The derivative of a complex function splits into those of its real and imaginary parts. -/
theorem bsg_fderiv_split {θ : Space → ℂ} (hθ : ContDiff ℝ ∞ θ) (j : Fin 3) (y : Space) :
    fderiv ℝ θ y (EuclideanSpace.single j 1) =
      ((spatialTestDerivative j (fun y => (θ y).re) y : ℝ) : ℂ) +
        Complex.I * ((spatialTestDerivative j (fun y => (θ y).im) y : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ θ y := (hθ.differentiable (by simp)).differentiableAt
  have hre : fderiv ℝ (fun y => (θ y).re) y = Complex.reCLM.comp (fderiv ℝ θ y) :=
    (Complex.reCLM.hasFDerivAt.comp y hd.hasFDerivAt).fderiv
  have him : fderiv ℝ (fun y => (θ y).im) y = Complex.imCLM.comp (fderiv ℝ θ y) :=
    (Complex.imCLM.hasFDerivAt.comp y hd.hasFDerivAt).fderiv
  simp only [spatialTestDerivative, coordinateVector, hre, him, ContinuousLinearMap.comp_apply,
    Complex.reCLM_apply, Complex.imCLM_apply]
  rw [mul_comm]
  exact (Complex.re_add_im _).symm

/-- `BSGKernelCplx`: `∫ K_c(y - z) ∂ⱼθ(y) dy = T_{cj} θ(z)`. -/
theorem bsgKernelCplx : BSGKernelCplx := by
  intro θ hθ hθc c j z
  have hu := bsg_isSpatialTest_re hθ hθc
  have hv := bsg_isSpatialTest_im hθ hθc
  have i1 : Integrable (fun y : Space => (((4 * Real.pi)⁻¹ * (‖y - z‖ ^ 3)⁻¹ * (y - z) c *
      spatialTestDerivative j (fun y => (θ y).re) y : ℝ) : ℂ)) :=
    (bsg_integrable_kernel c z (hu.derivative j)).ofReal
  have i2 : Integrable (fun y : Space => (((4 * Real.pi)⁻¹ * (‖y - z‖ ^ 3)⁻¹ * (y - z) c *
      spatialTestDerivative j (fun y => (θ y).im) y : ℝ) : ℂ)) :=
    (bsg_integrable_kernel c z (hv.derivative j)).ofReal
  have e : (fun y : Space => bsKernel (y - z) c * fderiv ℝ θ y (EuclideanSpace.single j 1)) =
      fun y : Space =>
        (((4 * Real.pi)⁻¹ * (‖y - z‖ ^ 3)⁻¹ * (y - z) c *
          spatialTestDerivative j (fun y => (θ y).re) y : ℝ) : ℂ) +
        Complex.I * (((4 * Real.pi)⁻¹ * (‖y - z‖ ^ 3)⁻¹ * (y - z) c *
          spatialTestDerivative j (fun y => (θ y).im) y : ℝ) : ℂ) := by
    funext y
    rw [bsg_fderiv_split hθ j y]
    simp only [bsKernel, PiLp.toLp_apply]
    push_cast
    ring
  rw [e, integral_add i1 (i2.const_mul Complex.I), integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal, bsgKernelReal _ hu c j z,
    bsgKernelReal _ hv c j z]
  rfl

/-- Complexified real duality: `∫ u R_{jc} g = ∫ T_{cj} u g` with complex-valued integrands. -/
theorem bsg_dualReal_ofReal {u : Space → ℝ} (hu : IsSpatialTest u) (g : ScalarL2) (c j : Fin 3) :
    ∫ y : Space, ((u y : ℝ) : ℂ) * ((rieszPairL2 j c g y : ℝ) : ℂ) =
      ∫ y : Space, ((rieszPairTest c j u y : ℝ) : ℂ) * ((g y : ℝ) : ℂ) := by
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal, integral_complex_ofReal, bsgDualReal u hu g c j]

/-- The four-term expansion of an integral of `(a + i b)(c + i d)`. -/
theorem bsg_integral_four {a1 a2 a3 a4 : Space → ℂ} (h1 : Integrable a1) (h2 : Integrable a2)
    (h3 : Integrable a3) (h4 : Integrable a4) :
    ∫ y : Space, (a1 y + Complex.I * a2 y + Complex.I * a3 y - a4 y) =
      (∫ y : Space, a1 y) + Complex.I * (∫ y : Space, a2 y) + Complex.I * (∫ y : Space, a3 y) -
        ∫ y : Space, a4 y := by
  have hB : Integrable (fun y : Space => a1 y + Complex.I * a2 y) := h1.add (h2.const_mul _)
  have hA : Integrable (fun y : Space => a1 y + Complex.I * a2 y + Complex.I * a3 y) :=
    hB.add (h3.const_mul _)
  rw [integral_sub hA h4, integral_add hB (h3.const_mul _), integral_add h1 (h2.const_mul _),
    integral_const_mul, integral_const_mul]

/-- The four real pairings assembled: `∫ (u + i v) R(g) = ∫ (T u + i T v) g`. -/
theorem bsg_dualCplx_core {u v : Space → ℝ} (hu : IsSpatialTest u) (hv : IsSpatialTest v)
    (g : BsgCL2) (c j : Fin 3) :
    ∫ y : Space, (((u y : ℝ) : ℂ) + Complex.I * ((v y : ℝ) : ℂ)) *
        bsgCplxOp (rieszPairL2 j c) g y =
      ∫ y : Space, (((rieszPairTest c j u y : ℝ) : ℂ) +
        Complex.I * ((rieszPairTest c j v y : ℝ) : ℂ)) * g y := by
  have iA : ∀ (w : Space → ℝ), IsSpatialTest w → ∀ h : ScalarL2,
      Integrable (fun y : Space => ((w y : ℝ) : ℂ) * ((rieszPairL2 j c h y : ℝ) : ℂ)) :=
    fun w hw h => by
      have h0 : Integrable (fun y : Space => w y * rieszPairL2 j c h y) :=
        (hw.memLp 2).integrable_mul (Lp.memLp (rieszPairL2 j c h))
      have h1 : Integrable (fun y : Space => ((w y * rieszPairL2 j c h y : ℝ) : ℂ)) := h0.ofReal
      exact h1.congr (Eventually.of_forall fun y => by simp only [Complex.ofReal_mul])
  have iB : ∀ (w : Space → ℝ), IsSpatialTest w → ∀ h : ScalarL2,
      Integrable (fun y : Space => ((rieszPairTest c j w y : ℝ) : ℂ) * ((h y : ℝ) : ℂ)) :=
    fun w hw h => by
      have h0 : Integrable (fun y : Space => rieszPairTest c j w y * h y) :=
        (memLp_rieszPairTest hw c j).integrable_mul (Lp.memLp h)
      have h1 : Integrable (fun y : Space => ((rieszPairTest c j w y * h y : ℝ) : ℂ)) := h0.ofReal
      exact h1.congr (Eventually.of_forall fun y => by simp only [Complex.ofReal_mul])
  have eL : (fun y : Space => (((u y : ℝ) : ℂ) + Complex.I * ((v y : ℝ) : ℂ)) *
      bsgCplxOp (rieszPairL2 j c) g y) =ᵐ[volume] fun y : Space =>
      ((u y : ℝ) : ℂ) * ((rieszPairL2 j c (bsgReL2 g) y : ℝ) : ℂ) +
        Complex.I * (((u y : ℝ) : ℂ) * ((rieszPairL2 j c (bsgImL2 g) y : ℝ) : ℂ)) +
        Complex.I * (((v y : ℝ) : ℂ) * ((rieszPairL2 j c (bsgReL2 g) y : ℝ) : ℂ)) -
          ((v y : ℝ) : ℂ) * ((rieszPairL2 j c (bsgImL2 g) y : ℝ) : ℂ) := by
    filter_upwards [bsgCplxOp_ae (rieszPairL2 j c) g] with y hy
    rw [hy]
    linear_combination (((v y : ℝ) : ℂ) * ((rieszPairL2 j c (bsgImL2 g) y : ℝ) : ℂ)) *
      Complex.I_sq
  have eR : (fun y : Space => (((rieszPairTest c j u y : ℝ) : ℂ) +
      Complex.I * ((rieszPairTest c j v y : ℝ) : ℂ)) * g y) =ᵐ[volume] fun y : Space =>
      ((rieszPairTest c j u y : ℝ) : ℂ) * ((bsgReL2 g y : ℝ) : ℂ) +
        Complex.I * (((rieszPairTest c j u y : ℝ) : ℂ) * ((bsgImL2 g y : ℝ) : ℂ)) +
        Complex.I * (((rieszPairTest c j v y : ℝ) : ℂ) * ((bsgReL2 g y : ℝ) : ℂ)) -
          ((rieszPairTest c j v y : ℝ) : ℂ) * ((bsgImL2 g y : ℝ) : ℂ) := by
    filter_upwards [bsgReL2_ae g, bsgImL2_ae g] with y h1 h2
    have hgy : g y = ((bsgReL2 g y : ℝ) : ℂ) + Complex.I * ((bsgImL2 g y : ℝ) : ℂ) := by
      rw [h1, h2, mul_comm]
      exact (Complex.re_add_im _).symm
    rw [hgy]
    linear_combination (((rieszPairTest c j v y : ℝ) : ℂ) * ((bsgImL2 g y : ℝ) : ℂ)) *
      Complex.I_sq
  rw [integral_congr_ae eL, integral_congr_ae eR,
    bsg_integral_four (iA u hu _) (iA u hu _) (iA v hv _) (iA v hv _),
    bsg_integral_four (iB u hu _) (iB u hu _) (iB v hv _) (iB v hv _),
    bsg_dualReal_ofReal hu (bsgReL2 g) c j, bsg_dualReal_ofReal hu (bsgImL2 g) c j,
    bsg_dualReal_ofReal hv (bsgReL2 g) c j, bsg_dualReal_ofReal hv (bsgImL2 g) c j]

/-- `BSGDualCplx`: `∫ θ R_{jc} g = ∫ T_{cj} θ g`. -/
theorem bsgDualCplx : BSGDualCplx := by
  intro θ hθ hθc g c j
  have h := bsg_dualCplx_core (bsg_isSpatialTest_re hθ hθc) (bsg_isSpatialTest_im hθ hθc) g c j
  have e : (fun y : Space => θ y * bsgCplxOp (rieszPairL2 j c) g y) =
      fun y : Space => ((((θ y).re : ℝ) : ℂ) + Complex.I * (((θ y).im : ℝ) : ℂ)) *
        bsgCplxOp (rieszPairL2 j c) g y := by
    funext y
    congr 1
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  rw [e, h]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
