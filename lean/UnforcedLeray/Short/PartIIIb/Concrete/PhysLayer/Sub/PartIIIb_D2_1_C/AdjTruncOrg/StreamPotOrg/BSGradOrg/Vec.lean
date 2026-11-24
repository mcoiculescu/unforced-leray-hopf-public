import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.BSGradOrg.Cplx

/-!
# `BSGrad` ingredients: the vector identities

Source `the November 2 reference manuscript` lines 1351-1362.

* `bsgKernelVec`: `∫ K(y - z) × ∂ⱼθ(y) dy = W_j θ(z)`, from the expansion
  `w × a = -∑_{c,b} w_c (a · (e_c × e_b)) e_b` and `bsgKernelCplx`;
* `bsgDualVec`: `∫ f · W_j θ = -∫ θ · bsGradL2 j f`, from `bsGradL2_ae` and `bsgDualCplx`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

/-- `w × a = -∑_{c,b} w_c (a · (e_c × e_b)) e_b`. -/
theorem bsg_cross_expand (w a : CVec3) :
    crossC w a =
      -∑ c : Fin 3, ∑ b : Fin 3, (w c * dotL a (crossC (bsgE c) (bsgE b))) • bsgE b := by
  ext i
  fin_cases i <;>
    simp [crossC, dotL_apply, Fin.sum_univ_three, bsgE] <;> ring

theorem bsg_coef_eq (c b : Fin 3) (θ : Space → CVec3) :
    bsgCoef c b θ = fun y => ((dotL.flip (crossC (bsgE c) (bsgE b))).restrictScalars ℝ) (θ y) :=
  rfl

theorem bsg_coef_contDiff {θ : Space → CVec3} (hθ : ContDiff ℝ ∞ θ) (c b : Fin 3) :
    ContDiff ℝ ∞ (bsgCoef c b θ) := by
  rw [bsg_coef_eq]
  exact ((dotL.flip (crossC (bsgE c) (bsgE b))).restrictScalars ℝ).contDiff.comp hθ

theorem bsg_coef_hasCompactSupport {θ : Space → CVec3} (hθc : HasCompactSupport θ) (c b : Fin 3) :
    HasCompactSupport (bsgCoef c b θ) :=
  hθc.comp_left (g := fun a : CVec3 => dotL a (crossC (bsgE c) (bsgE b))) (by simp)

theorem bsg_fderiv_coef {θ : Space → CVec3} (hθ : ContDiff ℝ ∞ θ) (c b j : Fin 3) (y : Space) :
    fderiv ℝ (bsgCoef c b θ) y (EuclideanSpace.single j 1) =
      dotL (fderiv ℝ θ y (EuclideanSpace.single j 1)) (crossC (bsgE c) (bsgE b)) := by
  have hd : DifferentiableAt ℝ θ y := (hθ.differentiable (by simp)).differentiableAt
  have h : HasFDerivAt (bsgCoef c b θ)
      (((dotL.flip (crossC (bsgE c) (bsgE b))).restrictScalars ℝ).comp (fderiv ℝ θ y)) y :=
    (((dotL.flip (crossC (bsgE c) (bsgE b))).restrictScalars ℝ).hasFDerivAt).comp y
      hd.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- The complex kernel integrand is integrable. -/
theorem bsg_integrable_kernelCplx {θ : Space → ℂ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (c j : Fin 3) (z : Space) :
    Integrable (fun y : Space => bsKernel (y - z) c * fderiv ℝ θ y (EuclideanSpace.single j 1)) := by
  have hu := bsg_isSpatialTest_re hθ hθc
  have hv := bsg_isSpatialTest_im hθ hθc
  have i1 : Integrable (fun y : Space => (((4 * Real.pi)⁻¹ * (‖y - z‖ ^ 3)⁻¹ * (y - z) c *
      spatialTestDerivative j (fun y => (θ y).re) y : ℝ) : ℂ)) :=
    (bsg_integrable_kernel c z (hu.derivative j)).ofReal
  have i2 : Integrable (fun y : Space => (((4 * Real.pi)⁻¹ * (‖y - z‖ ^ 3)⁻¹ * (y - z) c *
      spatialTestDerivative j (fun y => (θ y).im) y : ℝ) : ℂ)) :=
    (bsg_integrable_kernel c z (hv.derivative j)).ofReal
  refine (i1.add (i2.const_mul Complex.I)).congr (Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply]
  rw [bsg_fderiv_split hθ j y]
  simp only [bsKernel, PiLp.toLp_apply]
  push_cast
  ring

/-- `BSGKernelVec`: `∫ K(y - z) × ∂ⱼθ(y) dy = W_j θ(z)`. -/
theorem bsgKernelVec : BSGKernelVec := by
  intro θ hθ hθc j z
  have hint : ∀ c b : Fin 3, Integrable (fun y : Space =>
      (bsKernel (y - z) c * fderiv ℝ (bsgCoef c b θ) y (EuclideanSpace.single j 1)) • bsgE b) :=
    fun c b => (bsg_integrable_kernelCplx (bsg_coef_contDiff hθ c b)
      (bsg_coef_hasCompactSupport hθc c b) c j z).smul_const _
  have hint2 : ∀ c : Fin 3, Integrable (fun y : Space => ∑ b : Fin 3,
      (bsKernel (y - z) c * fderiv ℝ (bsgCoef c b θ) y (EuclideanSpace.single j 1)) • bsgE b) :=
    fun c => integrable_finsetSum _ fun b _ => hint c b
  have e : (fun y : Space => crossC (bsKernel (y - z)) (fderiv ℝ θ y (EuclideanSpace.single j 1))) =
      fun y : Space => -∑ c : Fin 3, ∑ b : Fin 3,
        (bsKernel (y - z) c * fderiv ℝ (bsgCoef c b θ) y (EuclideanSpace.single j 1)) • bsgE b := by
    funext y
    rw [bsg_cross_expand]
    simp only [bsg_fderiv_coef hθ]
  rw [e, integral_neg, integral_finsetSum _ fun c _ => hint2 c]
  unfold bsgW
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun b _ => hint c b]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_smul_const, bsgKernelCplx _ (bsg_coef_contDiff hθ c b)
    (bsg_coef_hasCompactSupport hθc c b) c j z]

theorem bsg_dotL_single (a : CVec3) (b : Fin 3) : dotL a (bsgE b) = a b := by
  simp [dotL_apply, bsgE]

/-- `BSGDualVec`: `∫ f · W_j θ = -∫ θ · bsGradL2 j f`. -/
theorem bsgDualVec : BSGDualVec := by
  intro θ hθ hθc f hf j
  have hfb : ∀ b : Fin 3, MemLp (fun y => f y b) 2 volume := fun b =>
    ((EuclideanSpace.proj b : CVec3 →L[ℂ] ℂ).comp_memLp' hf)
  have hH : ∀ c b : Fin 3, MemLp (bsgHess c j (bsgCoef c b θ)) 2 volume := fun c b =>
    bsgHessMemLp _ (bsg_coef_contDiff hθ c b) (bsg_coef_hasCompactSupport hθc c b) c j
  have hC : ∀ c b : Fin 3, MemLp (bsgCoef c b θ) 2 volume := fun c b =>
    (bsg_coef_contDiff hθ c b).continuous.memLp_of_hasCompactSupport
      (bsg_coef_hasCompactSupport hθc c b)
  have iL : ∀ c b : Fin 3,
      Integrable (fun z : Space => bsgHess c j (bsgCoef c b θ) z * f z b) := fun c b =>
    (hH c b).integrable_mul (hfb b)
  have iR : ∀ c b : Fin 3, Integrable (fun y : Space =>
      bsgCoef c b θ y * bsgCplxOp (rieszPairL2 j c) (bsgCoord b (hf.toLp f)) y) := fun c b =>
    (hC c b).integrable_mul (Lp.memLp _)
  have eL : (fun z : Space => dotL (f z) (bsgW j θ z)) = fun z : Space =>
      -∑ c : Fin 3, ∑ b : Fin 3, bsgHess c j (bsgCoef c b θ) z * f z b := by
    funext z
    simp only [bsgW, map_neg, map_sum, map_smul, smul_eq_mul, bsg_dotL_single]
  have eR : (fun y : Space => dotL (θ y) (bsGradL2 j (hf.toLp f) y)) =ᵐ[volume] fun y : Space =>
      ∑ c : Fin 3, ∑ b : Fin 3,
        bsgCoef c b θ y * bsgCplxOp (rieszPairL2 j c) (bsgCoord b (hf.toLp f)) y := by
    filter_upwards [bsGradL2_ae j (hf.toLp f)] with y hy
    rw [hy, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  rw [eL, integral_neg, integral_congr_ae eR,
    integral_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ => iL c b,
    integral_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ => iR c b]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun b _ => iL c b, integral_finsetSum _ fun b _ => iR c b]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [bsgDualCplx _ (bsg_coef_contDiff hθ c b) (bsg_coef_hasCompactSupport hθc c b)
    (bsgCoord b (hf.toLp f)) c j]
  refine integral_congr_ae ?_
  filter_upwards [bsgCoord_ae b (hf.toLp f), hf.coeFn_toLp] with y h1 h2
  rw [h1, h2]

end UnforcedLeray.Short.PartIIIb.Concrete
