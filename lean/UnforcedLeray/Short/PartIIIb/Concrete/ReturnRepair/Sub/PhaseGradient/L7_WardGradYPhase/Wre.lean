import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise.Decay

/-!
# `PartIII-b:C/rep/2/7`, the field `Re W_μ`: smoothness, divergence, axisymmetry, decay

Source `the November 2 reference manuscript` 4175-4186, 4199-4200.
The analogues for the single response `sepWre ν μ T = Re W_μ` of the facts about `sepX0` in
`PartIII-b_C_rep_2_5/Pointwise/{Source,Decay}.lean`; they give the two partial derivatives of the
outward primitive `Ψ_{Re W_μ}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem wgyw_contDiffOn {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) :
    ContDiffOn ℝ 2 (sepWre ν μ T τ) {y : Space | rOut < ϱ y} := by
  have hA := sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν (by simpa using hμ) hr
    hP hS hM τ
  refine contDiffOn_piLp' 2 fun i => ?_
  have := Complex.reCLM.contDiff.comp_contDiffOn (hA i)
  refine this.congr fun y _ => ?_
  simp [sepWre]

lemma wgyw_re_fderiv (A : Space → ℂ) (y : Space) (hA : DifferentiableAt ℝ A y) (v : Space) :
    fderiv ℝ (fun x => (A x).re) y v = (fderiv ℝ A y v).re := by
  have hre : HasFDerivAt (fun x => (A x).re) (Complex.reCLM.comp (fderiv ℝ A y)) y :=
    Complex.reCLM.hasFDerivAt.comp y hA.hasFDerivAt
  rw [hre.fderiv]
  simp

theorem wgyw_div {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) (y : Space)
    (hyr : rOut < ϱ y) :
    ∑ j : Fin 3, physPd (sepWre ν μ T τ) j y j = 0 := by
  have hμ0 : -(1 / 4) < (μ : ℂ).re := by simpa using hμ
  have hD0 := sepWDivFree_all ν (μ : ℂ) rOut P T hν hμ0 hr hP hS hM τ y hyr
  have hsm0 := sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν hμ0 hr hP hS hM τ
  have hopen : IsOpen {y : Space | rOut < ϱ y} :=
    isOpen_lt continuous_const (by unfold ϱ; fun_prop)
  have hdA : ∀ i, DifferentiableAt ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ i) y := fun i =>
    ((hsm0 i).differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hyr)
  have hF : DifferentiableAt ℝ (fun y' => sepWre ν μ T τ y') y := by
    rw [differentiableAt_piLp]
    intro i
    exact Complex.reCLM.differentiableAt.comp y (hdA i)
  have hcomp : ∀ j : Fin 3, physPd (sepWre ν μ T τ) j y j =
      (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ j) y (coordinateVector j)).re := by
    intro j
    unfold physPd
    rw [wgx_coord_fderiv _ y hF _ j]
    exact wgyw_re_fderiv _ y (hdA j) _
  calc ∑ j : Fin 3, physPd (sepWre ν μ T τ) j y j
      = ∑ j : Fin 3, (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ j) y
          (coordinateVector j)).re := Finset.sum_congr rfl fun j _ => hcomp j
    _ = 0 := by
        rw [← Complex.re_sum, hD0]
        simp

theorem wgyw_equivariant (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M * M.transpose = 1)
    (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ τ z, T τ (actM M z) = M * T τ z * M.transpose) (y : Space) (τ : ℝ)
    (hI1 : SepIntegrableAt ν (μ : ℂ) T y τ) :
    sepWre ν μ T τ (actM M y) = actM M (sepWre ν μ T τ y) := by
  have h1 := sepWEquivariance M hM ν (μ : ℂ) T hT y τ hI1
  unfold sepWre
  ext i
  simp only [h1]
  simp only [actM, Matrix.mulVec, dotProduct, PiLp.toLp_apply, WithLp.ofLp_toLp]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp

theorem wgyw_axi {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (hAx : IsAxiSource T)
    (τ : ℝ) (y : Space) (hyr : rOut < ϱ y) :
    sepWre ν μ T τ y = frameL y !₂[sepWre ν μ T τ (meridPt y) 0, sepWre ν μ T τ (meridPt y) 2] ∧
      ‖sepWre ν μ T τ (meridPt y)‖ = ‖sepWre ν μ T τ y‖ := by
  have hρ : 0 < ϱ y := lt_of_le_of_lt hr hyr
  have hρ2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  obtain ⟨hco, hmer⟩ := wgx_rot_meridPt hρ
  have hmr : rOut < ϱ (meridPt y) := by rw [varrho_meridPt]; exact hyr
  have hI1 := sepIntegrableOfSource_all ν (μ : ℂ) rOut P T hν (by simpa using hμ) hr hP hS hM τ
    (meridPt y) hmr
  have hfix : actM reflM (meridPt y) = meridPt y := by
    ext i
    fin_cases i <;> simp [actM, reflM, meridPt, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have e1 := wgyw_equivariant _ (rotM_orth hco) ν μ T (fun τ z => hAx.1 _ _ hco τ z)
    (meridPt y) τ hI1
  have e2 := wgyw_equivariant _ reflM_orth ν μ T (fun τ z => hAx.2 τ z) (meridPt y) τ hI1
  rw [hmer] at e1
  rw [hfix] at e2
  have h1 : sepWre ν μ T τ (meridPt y) 1 = 0 := by
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
