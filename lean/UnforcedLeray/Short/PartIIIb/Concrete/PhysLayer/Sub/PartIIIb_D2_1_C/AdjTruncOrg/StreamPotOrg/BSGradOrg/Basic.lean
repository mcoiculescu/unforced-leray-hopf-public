import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.BSGradOrg.Defs
import UnforcedLeray.Lib.CZL2.L2OffSupport

/-!
# `BSGrad` ingredients: the elementary ones

Source `the November 2 reference manuscript` lines 1351-1362.

* `bsgCoeFn`: a.e. formulas for the slice operators `bsgReL2`, `bsgImL2`, `bsgCplxOp`, `bsgCoord`,
  `bsGradL2`;
* `bsgKernelReal`: `∫ K_c(y - z) ∂ⱼw(y) dy = ∂_c∂ⱼ(N ∗ w)(z)` (`newtonConv_partial`);
* `bsgDualReal`: `∫ u R_{jc} g = ∫ T_{cj} u g` (`inner_rieszPairL2`, `rieszPairL2_toLp`);
* `bsgHessMemLp`: `T_{cj}` maps complex tests into `L²` (`memLp_rieszPairTest`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

theorem bsgReL2_ae (g : BsgCL2) : (bsgReL2 g : Space → ℝ) =ᵐ[volume] fun y => (g y).re := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL Complex.reCLM g] with y hy
  rw [bsgReL2, hy]
  rfl

theorem bsgImL2_ae (g : BsgCL2) : (bsgImL2 g : Space → ℝ) =ᵐ[volume] fun y => (g y).im := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL Complex.imCLM g] with y hy
  rw [bsgImL2, hy]
  rfl

theorem bsgOfRealL2_ae (h : ScalarL2) :
    (bsgOfRealL2 h : Space → ℂ) =ᵐ[volume] fun y => ((h y : ℝ) : ℂ) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM h] with y hy
  rw [bsgOfRealL2, hy]
  rfl

theorem bsgIOfRealL2_ae (h : ScalarL2) :
    (bsgIOfRealL2 h : Space → ℂ) =ᵐ[volume] fun y => Complex.I * ((h y : ℝ) : ℂ) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) Complex.I) h] with y hy
  rw [bsgIOfRealL2, hy]
  simp [Complex.real_smul, mul_comm]

theorem bsgCplxOp_ae (R : ScalarL2 →L[ℝ] ScalarL2) (g : BsgCL2) :
    (bsgCplxOp R g : Space → ℂ) =ᵐ[volume]
      fun y => ((R (bsgReL2 g) y : ℝ) : ℂ) + Complex.I * ((R (bsgImL2 g) y : ℝ) : ℂ) := by
  have e : bsgCplxOp R g = bsgOfRealL2 (R (bsgReL2 g)) + bsgIOfRealL2 (R (bsgImL2 g)) := rfl
  rw [e]
  filter_upwards [Lp.coeFn_add (bsgOfRealL2 (R (bsgReL2 g))) (bsgIOfRealL2 (R (bsgImL2 g))),
    bsgOfRealL2_ae (R (bsgReL2 g)), bsgIOfRealL2_ae (R (bsgImL2 g))] with y h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]

theorem bsgCoord_ae (b : Fin 3) (F : BsgVL2) :
    (bsgCoord b F : Space → ℂ) =ᵐ[volume] fun y => F y b := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    ((EuclideanSpace.proj b : CVec3 →L[ℂ] ℂ).restrictScalars ℝ) F] with y hy
  rw [bsgCoord, hy]
  rfl

theorem bsgEmb_ae (v : CVec3) (h : BsgCL2) :
    (bsgEmb v h : Space → CVec3) =ᵐ[volume] fun y => h y • v := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) v).restrictScalars ℝ) h] with y hy
  rw [bsgEmb, hy]
  simp

theorem bsGradL2_ae (j : Fin 3) (F : BsgVL2) :
    (bsGradL2 j F : Space → CVec3) =ᵐ[volume] fun y =>
      ∑ c : Fin 3, ∑ b : Fin 3, bsgCplxOp (rieszPairL2 j c) (bsgCoord b F) y •
        crossC (bsgE c) (bsgE b) := by
  set X : Fin 3 → Fin 3 → BsgVL2 := fun c b =>
    bsgEmb (crossC (bsgE c) (bsgE b)) (bsgCplxOp (rieszPairL2 j c) (bsgCoord b F)) with hX
  have e : bsGradL2 j F = ∑ c : Fin 3, ∑ b : Fin 3, X c b := by
    simp [bsGradL2, hX]
  rw [e]
  have h1 := Lp.coeFn_fun_finsetSum Finset.univ (fun c : Fin 3 => ∑ b : Fin 3, X c b)
  have h2 : ∀ᵐ y ∂(volume : Measure Space), ∀ c : Fin 3,
      (⇑(∑ b : Fin 3, X c b) : Space → CVec3) y = ∑ b : Fin 3, (X c b : Space → CVec3) y :=
    ae_all_iff.mpr fun c => Lp.coeFn_fun_finsetSum Finset.univ (X c)
  have h3 : ∀ᵐ y ∂(volume : Measure Space), ∀ c b : Fin 3, (X c b : Space → CVec3) y =
      bsgCplxOp (rieszPairL2 j c) (bsgCoord b F) y • crossC (bsgE c) (bsgE b) :=
    ae_all_iff.mpr fun c => ae_all_iff.mpr fun b => bsgEmb_ae _ _
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  rw [hy1]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hy2 c]
  exact Finset.sum_congr rfl fun b _ => hy3 c b

/-- The a.e. formulas of `BSGCoeFn`. -/
theorem bsgCoeFn : BSGCoeFn :=
  ⟨bsgReL2_ae, bsgImL2_ae, bsgCplxOp_ae, bsgCoord_ae, bsGradL2_ae⟩

/-- `BSGKernelReal`: `∫ K_c(y - z) ∂ⱼw(y) dy = ∂_c∂ⱼ(N ∗ w)(z)`. -/
theorem bsgKernelReal : BSGKernelReal := by
  intro w hw c j z
  have h1 : ∀ y : Space,
      (4 * Real.pi)⁻¹ * (‖y - z‖ ^ 3)⁻¹ * (y - z) c * spatialTestDerivative j w y =
        -(UnforcedLeray.PressureAnalysis.newtonGradientKernel c (y - z) *
          spatialTestDerivative j w y) := by
    intro y
    simp only [UnforcedLeray.PressureAnalysis.newtonGradientKernel]
    ring
  simp_rw [h1]
  rw [integral_neg, rieszPairTest_eq_newtonConv hw c j,
    newtonConv_partial (hw.derivative j) c z]
  rfl

/-- `BSGDualReal`: `∫ u R_{jc} g = ∫ T_{cj} u g`. -/
theorem bsgDualReal : BSGDualReal := by
  intro u hu g c j
  have h := inner_rieszPairL2 j c ((hu.memLp 2).toLp u) g
  rw [rieszPairL2_toLp hu c j, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at h
  have e1 : ∫ y : Space, u y * rieszPairL2 j c g y =
      ∫ y : Space, inner ℝ (((hu.memLp 2).toLp u : Space → ℝ) y)
        ((rieszPairL2 j c g : Space → ℝ) y) := by
    refine integral_congr_ae ?_
    filter_upwards [(hu.memLp 2).coeFn_toLp] with y hy
    rw [hy, Real.inner_apply]
  have e2 : ∫ y : Space, rieszPairTest c j u y * g y =
      ∫ y : Space, inner ℝ (((memLp_rieszPairTest hu c j).toLp (rieszPairTest c j u) :
        Space → ℝ) y) ((g : Space → ℝ) y) := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_rieszPairTest hu c j).coeFn_toLp] with y hy
    rw [hy, Real.inner_apply]
  rw [e1, e2, h]

/-- Real and imaginary parts of a complex compact smooth function are spatial tests. -/
theorem bsg_isSpatialTest_re {θ : Space → ℂ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) :
    IsSpatialTest (fun y => (θ y).re) :=
  ⟨Complex.reCLM.contDiff.comp hθ, hθc.comp_left Complex.zero_re⟩

theorem bsg_isSpatialTest_im {θ : Space → ℂ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) :
    IsSpatialTest (fun y => (θ y).im) :=
  ⟨Complex.imCLM.contDiff.comp hθ, hθc.comp_left Complex.zero_im⟩

/-- `BSGHessMemLp`: `T_{cj} θ ∈ L²`. -/
theorem bsgHessMemLp : BSGHessMemLp := by
  intro θ hθ hθc c j
  exact ((memLp_rieszPairTest (bsg_isSpatialTest_re hθ hθc) c j).ofReal (K := ℂ)).add
    (((memLp_rieszPairTest (bsg_isSpatialTest_im hθ hθc) c j).ofReal (K := ℂ)).const_mul
      Complex.I)

end UnforcedLeray.Short.PartIIIb.Concrete
