import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3b
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3c
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T9
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.L1_far
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.IntAll
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K2
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `PartIII-b:C/rep/2/5`, pointwise leaf: the separated field `X₀ = sepX0` (source 4161-4192)

For a separated source `T` (`IsSepSource P (R√(5ν/6))`, finite `Y₂` moment, axisymmetric), the real
field `X₀(τ) = sepX0 ν μ T τ` is `C²` and divergence free on the young region, the frame lift of
its trace on `φ = 0`, has the same norm on the trace point (rotation), and satisfies `StreamDecay`;
hence the two partial derivatives of the outward primitive hold.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `X₀` is `C²` off the source disk. -/
theorem wgx_sepX0_contDiffOn {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) :
    ContDiffOn ℝ 2 (sepX0 ν μ T τ) {y : Space | rOut < ϱ y} := by
  have hA := sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν (by simpa using hμ) hr
    hP hS hM τ
  have hB := sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) rOut P T hν
    (by simp; linarith) hr hP hS hM τ
  refine contDiffOn_piLp' 2 fun i => ?_
  have hd := (hA i).sub (hB i)
  have := Complex.reCLM.contDiff.comp_contDiffOn hd
  refine this.congr fun y _ => ?_
  simp [sepX0]

/-- The `j`-th component of a derivative is the derivative of the `j`-th component. -/
lemma wgx_coord_fderiv (F : Space → Space) (y : Space) (hF : DifferentiableAt ℝ F y) (v : Space)
    (j : Fin 3) : fderiv ℝ F y v j = fderiv ℝ (fun x => F x j) y v := by
  have h : HasFDerivAt (fun x => (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (F x))
      ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (fderiv ℝ F y)) y :=
    ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt).comp y hF.hasFDerivAt
  have hfun : (fun x => F x j) = fun x => (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (F x) := rfl
  rw [hfun, h.fderiv]
  simp

/-- The derivative of a real part of a difference of two complex fields. -/
lemma wgx_re_sub_fderiv (A B : Space → ℂ) (y : Space) (hA : DifferentiableAt ℝ A y)
    (hB : DifferentiableAt ℝ B y) (v : Space) :
    fderiv ℝ (fun x => (A x - B x).re) y v = (fderiv ℝ A y v - fderiv ℝ B y v).re := by
  have hG : HasFDerivAt (fun x => A x - B x) (fderiv ℝ A y - fderiv ℝ B y) y :=
    hA.hasFDerivAt.sub hB.hasFDerivAt
  have hre : HasFDerivAt (fun x => (A x - B x).re)
      (Complex.reCLM.comp (fderiv ℝ A y - fderiv ℝ B y)) y :=
    Complex.reCLM.hasFDerivAt.comp y hG
  rw [hre.fderiv]
  simp

/-- `X₀` is divergence free off the source disk. -/
theorem wgx_sepX0_div {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) (y : Space)
    (hyr : rOut < ϱ y) :
    ∑ j : Fin 3, physPd (sepX0 ν μ T τ) j y j = 0 := by
  have hμ0 : -(1 / 4) < (μ : ℂ).re := by simpa using hμ
  have hμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hD0 := sepWDivFree_all ν (μ : ℂ) rOut P T hν hμ0 hr hP hS hM τ y hyr
  have hD1 := sepWDivFree_all ν ((μ : ℂ) + 1) rOut P T hν hμ1 hr hP hS hM τ y hyr
  have hsm0 := sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν hμ0 hr hP hS hM τ
  have hsm1 := sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) rOut P T hν hμ1 hr hP hS hM τ
  have hopen : IsOpen {y : Space | rOut < ϱ y} :=
    isOpen_lt continuous_const (by unfold ϱ; fun_prop)
  have hdA : ∀ i, DifferentiableAt ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ i) y := fun i =>
    ((hsm0 i).differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hyr)
  have hdB : ∀ i, DifferentiableAt ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T y' τ i) y := fun i =>
    ((hsm1 i).differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hyr)
  have hF : DifferentiableAt ℝ (fun y' => sepX0 ν μ T τ y') y := by
    rw [differentiableAt_piLp]
    intro i
    exact Complex.reCLM.differentiableAt.comp y ((hdA i).sub (hdB i))
  have hcomp : ∀ j : Fin 3, physPd (sepX0 ν μ T τ) j y j =
      (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ j) y (coordinateVector j) -
        fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T y' τ j) y (coordinateVector j)).re := by
    intro j
    unfold physPd
    rw [wgx_coord_fderiv _ y hF _ j]
    exact wgx_re_sub_fderiv _ _ y (hdA j) (hdB j) _
  calc ∑ j : Fin 3, physPd (sepX0 ν μ T τ) j y j
      = ∑ j : Fin 3, (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ j) y
          (coordinateVector j) - fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T y' τ j) y
          (coordinateVector j)).re := Finset.sum_congr rfl fun j _ => hcomp j
    _ = 0 := by
        rw [← Complex.re_sum, Finset.sum_sub_distrib, hD0, hD1]
        simp

/-- Rotation equivariance of `sepX0` at integrable points. -/
theorem wgx_sepX0_equivariant (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M * M.transpose = 1)
    (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ τ z, T τ (actM M z) = M * T τ z * M.transpose) (y : Space) (τ : ℝ)
    (hI1 : SepIntegrableAt ν (μ : ℂ) T y τ)
    (hI2 : SepIntegrableAt ν ((μ : ℂ) + 1) T y τ) :
    sepX0 ν μ T τ (actM M y) = actM M (sepX0 ν μ T τ y) := by
  have h1 := sepWEquivariance M hM ν (μ : ℂ) T hT y τ hI1
  have h2 := sepWEquivariance M hM ν ((μ : ℂ) + 1) T hT y τ hI2
  unfold sepX0
  ext i
  simp only [h1, h2]
  simp only [actM, Matrix.mulVec, dotProduct, PiLp.toLp_apply, WithLp.ofLp_toLp]
  rw [← Finset.sum_sub_distrib, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [mul_sub]

/-- A rotation about the vertical axis preserves the Euclidean norm. -/
theorem wgx_norm_actM_rot {co si : ℝ} (h : co ^ 2 + si ^ 2 = 1) (v : Space) :
    ‖actM (rotM co si) v‖ = ‖v‖ := by
  have key : ‖actM (rotM co si) v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, actM, rotM, Matrix.mulVec,
      dotProduct, PiLp.toLp_apply, WithLp.ofLp_toLp]
    simp [Matrix.of_apply, Matrix.cons_val', Fin.sum_univ_three]
    nlinarith [h]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 key

/-- The meridional trace point and the rotation carrying it to `y`. -/
theorem wgx_rot_meridPt {y : Space} (hy : 0 < ϱ y) :
    (y 0 / ϱ y) ^ 2 + (y 1 / ϱ y) ^ 2 = 1 ∧
      actM (rotM (y 0 / ϱ y) (y 1 / ϱ y)) (meridPt y) = y := by
  have hρ2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hco : (y 0 / ϱ y) ^ 2 + (y 1 / ϱ y) ^ 2 = 1 := by
    field_simp
    rw [hρ2]
  refine ⟨hco, ?_⟩
  ext i
  fin_cases i <;>
    simp [actM, rotM, meridPt, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    field_simp

/-- Frame form and norm of `X₀` at points of the young region. -/
theorem wgx_sepX0_axi {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (hAx : IsAxiSource T)
    (τ : ℝ) (y : Space) (hyr : rOut < ϱ y) :
    sepX0 ν μ T τ y = frameL y !₂[sepX0 ν μ T τ (meridPt y) 0, sepX0 ν μ T τ (meridPt y) 2] ∧
      ‖sepX0 ν μ T τ (meridPt y)‖ = ‖sepX0 ν μ T τ y‖ := by
  have hρ : 0 < ϱ y := lt_of_le_of_lt hr hyr
  have hρ2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  obtain ⟨hco, hmer⟩ := wgx_rot_meridPt hρ
  have hmr : rOut < ϱ (meridPt y) := by rw [varrho_meridPt]; exact hyr
  have hI1 := sepIntegrableOfSource_all ν (μ : ℂ) rOut P T hν (by simpa using hμ) hr hP hS hM τ
    (meridPt y) hmr
  have hI2 := sepIntegrableOfSource_all ν ((μ : ℂ) + 1) rOut P T hν (by simp; linarith) hr hP hS
    hM τ (meridPt y) hmr
  have hfix : actM reflM (meridPt y) = meridPt y := by
    ext i
    fin_cases i <;> simp [actM, reflM, meridPt, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have e1 := wgx_sepX0_equivariant _ (rotM_orth hco) ν μ T (fun τ z => hAx.1 _ _ hco τ z)
    (meridPt y) τ hI1 hI2
  have e2 := wgx_sepX0_equivariant _ reflM_orth ν μ T (fun τ z => hAx.2 τ z) (meridPt y) τ hI1 hI2
  rw [hmer] at e1
  rw [hfix] at e2
  have h1 : sepX0 ν μ T τ (meridPt y) 1 = 0 := by
    have := congrArg (fun w : Space => w 1) e2
    simp [actM, reflM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
    linarith
  refine ⟨?_, ?_⟩
  · rw [e1]
    ext i
    fin_cases i <;>
      simp [actM, rotM, frameL_apply, eR, hor, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1] <;>
      field_simp
  · rw [e1, wgx_norm_actM_rot hco]

end UnforcedLeray.Short.PartIIIb.Concrete

end
