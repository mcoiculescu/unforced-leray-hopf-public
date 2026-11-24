import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Int.Half
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T9

/-!
# Structure of `X₀ = sepX0`: solenoidal and axisymmetric swirl-free

Source `the November 2 reference manuscript` 3600-3610 (Leray kernel,
`∑_i ∂_iK_{ij} = 0`; `K_t(Mx) = M K_t(x) Mᵀ`), 4171-4178.  The statements of
`wardX0Structure_of` (`Sub/IIIb-D2_3_1_2.lean`), proved for the source `oldPhys`, are re-proved
for an arbitrary separated source `T` with `IsAxiSource T`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcr_divFree {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) {y : Space}
    (hy : rOut < ϱ y) : ∑ j : Fin 3, physPd (sepX0 ν μ T τ) j y j = 0 := by
  have hm1 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm2 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hopen : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hy' : y ∈ {y : Space | rOut < ϱ y} := hy
  have hA' := sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν hm1 hr hP hT hM τ
  have hB' := sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) rOut P T hν hm2 hr hP hT hM τ
  have dA : ∀ i, DifferentiableAt ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ i) y := fun i =>
    ((hA' i).contDiffAt (hopen.mem_nhds hy')).differentiableAt (by norm_num)
  have dB : ∀ i, DifferentiableAt ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T y' τ i) y := fun i =>
    ((hB' i).contDiffAt (hopen.mem_nhds hy')).differentiableAt (by norm_num)
  have hfun : sepX0 ν μ T τ = fun y' => (WithLp.toLp 2 fun i =>
      (IIIa.sepW ν (μ : ℂ) T y' τ i - IIIa.sepW ν ((μ : ℂ) + 1) T y' τ i).re : Space) := by
    funext y'
    rfl
  have hdiff : DifferentiableAt ℝ (sepX0 ν μ T τ) y := by
    rw [hfun]
    refine (differentiableAt_piLp 2).2 fun i => ?_
    exact Complex.reCLM.differentiableAt.comp y ((dA i).sub (dB i))
  unfold physPd
  have hc : ∀ j : Fin 3, fderiv ℝ (sepX0 ν μ T τ) y (UnforcedLeray.coordinateVector j) j =
      (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ j) y (UnforcedLeray.coordinateVector j) -
        fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T y' τ j) y
          (UnforcedLeray.coordinateVector j)).re := by
    intro j
    rw [fderiv_apply_coord _ _ _ _ hdiff, hfun]
    simp only
    have hh : HasFDerivAt (fun y' => (IIIa.sepW ν (μ : ℂ) T y' τ j -
        IIIa.sepW ν ((μ : ℂ) + 1) T y' τ j).re)
        (Complex.reCLM.comp ((fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ j) y) -
          (fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T y' τ j) y))) y :=
      Complex.reCLM.hasFDerivAt.comp y (((dA j).hasFDerivAt).sub ((dB j).hasFDerivAt))
    rw [hh.fderiv]
    simp
  simp only [hc]
  have e1 := sepWDivFree_all ν (μ : ℂ) rOut P T hν hm1 hr hP hT hM τ y hy
  have e2 := sepWDivFree_all ν ((μ : ℂ) + 1) rOut P T hν hm2 hr hP hT hM τ y hy
  rw [← Complex.re_sum, Finset.sum_sub_distrib, e1, e2]
  simp

theorem tcr_equivariant (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M * M.transpose = 1)
    (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (hT : ∀ τ z, T τ (actM M z) = M * T τ z * M.transpose) (y : Space)
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

theorem tcr_axi {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (hA : IsAxiSource T) (τ : ℝ)
    {y : Space} (hy : rOut < ϱ y) :
    sepX0 ν μ T τ y = frameL y !₂[sepX0 ν μ T τ (meridPt y) 0, sepX0 ν μ T τ (meridPt y) 2] := by
  have hm1 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm2 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hsq : 0 < y 0 ^ 2 + y 1 ^ 2 := by
    have h1 : 0 < ϱ y := lt_of_le_of_lt hr hy
    have h2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
    nlinarith
  have hρ : 0 < ϱ y := Real.sqrt_pos.2 hsq
  have hρ2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt hsq.le
  have hco : (y 0 / ϱ y) ^ 2 + (y 1 / ϱ y) ^ 2 = 1 := by
    field_simp
    rw [hρ2]
  have hmer : actM (rotM (y 0 / ϱ y) (y 1 / ϱ y)) (meridPt y) = y := by
    ext i
    fin_cases i <;>
      simp [actM, rotM, meridPt, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      field_simp
  have hfix : actM reflM (meridPt y) = meridPt y := by
    ext i
    fin_cases i <;> simp [actM, reflM, meridPt, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hmy : rOut < ϱ (meridPt y) := by rw [varrho_meridPt]; exact hy
  have hI1 := sepIntegrableOfSource_all ν (μ : ℂ) rOut P T hν hm1 hr hP hT hM τ _ hmy
  have hI2 := sepIntegrableOfSource_all ν ((μ : ℂ) + 1) rOut P T hν hm2 hr hP hT hM τ _ hmy
  have e1 := tcr_equivariant _ (rotM_orth hco) ν μ T τ (hA.1 _ _ hco) (meridPt y) hI1 hI2
  have e2 := tcr_equivariant _ reflM_orth ν μ T τ (hA.2) (meridPt y) hI1 hI2
  rw [hmer] at e1
  rw [hfix] at e2
  have h1 : sepX0 ν μ T τ (meridPt y) 1 = 0 := by
    have := congrArg (fun w : Space => w 1) e2
    simp [actM, reflM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
    linarith
  rw [e1]
  ext i
  fin_cases i <;>
    simp [actM, rotM, frameL_apply, eR, hor, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1] <;>
    field_simp

end UnforcedLeray.Short.PartIIIb.Concrete

end
