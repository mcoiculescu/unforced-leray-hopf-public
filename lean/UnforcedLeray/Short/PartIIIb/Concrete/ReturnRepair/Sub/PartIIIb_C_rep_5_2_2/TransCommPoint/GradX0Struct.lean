import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11_4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.Int
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `tcGradX0Struct` (`PartIII-b:C/rep/5/2/2/11/4/1`)

Source of record: `the November 2 reference manuscript` 3603-3647, 4171-4179.
Smoothness comes from `sepWSmoothOn_of` with `sepKernelBounds`, divergence freeness from
`sepWDivFree_all`, and the swirl-free condition from the equivariance of `sepX0` (the argument of
`wardX0Axi_of` repeated for a general separated source `T`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcg_re_fderiv (h : Space → ℂ) {y : Space} (hd : DifferentiableAt ℝ h y) (v : Space) :
    fderiv ℝ (fun y => (h y).re) y v = (fderiv ℝ h y v).re := by
  have hc := Complex.reCLM.hasFDerivAt.comp y hd.hasFDerivAt
  have e : fderiv ℝ (fun y => (h y).re) y = Complex.reCLM.comp (fderiv ℝ h y) := hc.fderiv
  rw [e]
  simp

theorem tcg_proj_fderiv (f : Space → Space) {y : Space} (hd : DifferentiableAt ℝ f y) (j : Fin 3)
    (v : Space) : fderiv ℝ (fun y => f y j) y v = fderiv ℝ f y v j := by
  have hc := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp y hd.hasFDerivAt
  have e : fderiv ℝ (fun y => f y j) y =
      (EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (fderiv ℝ f y) := hc.fderiv
  rw [e]
  simp

theorem tcg_rho_meridPt (y : Space) : ϱ (meridPt y) = ϱ y := by
  have h0 : (meridPt y) 0 = ϱ y := rfl
  have h1 : (meridPt y) 1 = 0 := rfl
  show √((meridPt y) 0 ^ 2 + (meridPt y) 1 ^ 2) = ϱ y
  rw [h0, h1, zero_pow two_ne_zero, add_zero, sq]
  exact Real.sqrt_mul_self (Real.sqrt_nonneg _)

theorem sepX0_equivariant (hS : SepWEquivariance) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M * M.transpose = 1) (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ τ z, T τ (actM M z) = M * T τ z * M.transpose) (τ : ℝ) (y : Space)
    (hI1 : SepIntegrableAt ν (μ : ℂ) T y τ) (hI2 : SepIntegrableAt ν ((μ : ℂ) + 1) T y τ) :
    sepX0 ν μ T τ (actM M y) = actM M (sepX0 ν μ T τ y) := by
  have h1 := hS M hM ν (μ : ℂ) T hT y τ hI1
  have h2 := hS M hM ν ((μ : ℂ) + 1) T hT y τ hI2
  unfold sepX0
  ext i
  simp only [h1, h2]
  simp only [actM, Matrix.mulVec, dotProduct, PiLp.toLp_apply, WithLp.ofLp_toLp]
  rw [← Finset.sum_sub_distrib, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [mul_sub]

theorem sepX0_axi (hS : SepWEquivariance) (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hAx : IsAxiSource T) (τ : ℝ) (y : Space) (hy : y ∉ axis)
    (hI1 : SepIntegrableAt ν (μ : ℂ) T (meridPt y) τ)
    (hI2 : SepIntegrableAt ν ((μ : ℂ) + 1) T (meridPt y) τ) :
    sepX0 ν μ T τ y = frameL y !₂[sepX0 ν μ T τ (meridPt y) 0, sepX0 ν μ T τ (meridPt y) 2] := by
  obtain ⟨hR, hF⟩ := hAx
  have hsq : 0 < y 0 ^ 2 + y 1 ^ 2 := by
    by_contra h
    apply hy
    have h0 : y 0 ^ 2 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have h1 : y 1 ^ 2 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    exact ⟨pow_eq_zero_iff (two_ne_zero) |>.1 h0, pow_eq_zero_iff (two_ne_zero) |>.1 h1⟩
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
  have e1 := sepX0_equivariant hS _ (rotM_orth hco) ν μ T (hR _ _ hco) τ (meridPt y) hI1 hI2
  have e2 := sepX0_equivariant hS _ reflM_orth ν μ T hF τ (meridPt y) hI1 hI2
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

/-- **`tcGradX0Struct`** (`PartIII-b:C/rep/5/2/2/11/4/1`): smoothness, divergence freeness and
swirl-freeness of `X₀ = sepX0` on the young region. -/
theorem tcGradX0Struct : TCGradX0Struct := by
  intro σ₁ σ₂ ν μ R P T τ y hctx
  obtain ⟨hσ1, hν, hν1, hR1, hP, hμI, hS, hM, hAx, hy⟩ := hctx
  have hμ : -(1 / 4 : ℝ) < μ := lt_of_lt_of_le hσ1 hμI.1
  have hμc : -(1 / 4 : ℝ) < ((μ : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact hμ
  have hμc' : -(1 / 4 : ℝ) < ((μ : ℂ) + 1).re := by
    rw [Complex.add_re, Complex.one_re, Complex.ofReal_re]; linarith
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hopen : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hSm : ∀ i : Fin 3, ContDiffOn ℝ 2 (fun y => IIIa.sepW ν (μ : ℂ) T y τ i) (youngOpen ν R) :=
    fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) _ P T hν hμc hr0 hP hS hM τ i
  have hSm' : ∀ i : Fin 3,
      ContDiffOn ℝ 2 (fun y => IIIa.sepW ν ((μ : ℂ) + 1) T y τ i) (youngOpen ν R) :=
    fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) _ P T hν hμc' hr0 hP hS hM τ i
  have hsmooth : ContDiffOn ℝ 2 (sepX0 ν μ T τ) (youngOpen ν R) := by
    refine (contDiffOn_piLp 2).2 fun i => ?_
    show ContDiffOn ℝ 2
      (fun x => (IIIa.sepW ν (μ : ℂ) T x τ i - IIIa.sepW ν ((μ : ℂ) + 1) T x τ i).re)
      (youngOpen ν R)
    exact Complex.reCLM.contDiff.comp_contDiffOn ((hSm i).sub (hSm' i))
  have hAd : ∀ i : Fin 3, ∀ y' ∈ youngOpen ν R,
      DifferentiableAt ℝ (fun y => IIIa.sepW ν (μ : ℂ) T y τ i) y' := fun i y' hy' =>
    ((hSm i).differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hy')
  have hBd : ∀ i : Fin 3, ∀ y' ∈ youngOpen ν R,
      DifferentiableAt ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) T y τ i) y' := fun i y' hy' =>
    ((hSm' i).differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hy')
  have hGd : ∀ y' ∈ youngOpen ν R, DifferentiableAt ℝ (sepX0 ν μ T τ) y' := fun y' hy' =>
    (hsmooth.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hy')
  refine ⟨hsmooth, ?_, ?_⟩
  · intro y' hy'
    have hy'' : R * Real.sqrt (5 * ν / 6) < ϱ y' := hy'
    have hA := sepWDivFree_all ν (μ : ℂ) _ P T hν hμc hr0 hP hS hM τ y' hy''
    have hB := sepWDivFree_all ν ((μ : ℂ) + 1) _ P T hν hμc' hr0 hP hS hM τ y' hy''
    have key : ∀ j : Fin 3, physPd (sepX0 ν μ T τ) j y' j =
        (fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) T y τ j) y' (coordinateVector j) -
          fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) T y τ j) y' (coordinateVector j)).re := by
      intro j
      unfold physPd
      rw [← tcg_proj_fderiv _ (hGd y' hy') j (coordinateVector j)]
      have e : (fun y => sepX0 ν μ T τ y j) =
          fun y => (IIIa.sepW ν (μ : ℂ) T y τ j - IIIa.sepW ν ((μ : ℂ) + 1) T y τ j).re := rfl
      have hd : DifferentiableAt ℝ
          (fun y => IIIa.sepW ν (μ : ℂ) T y τ j - IIIa.sepW ν ((μ : ℂ) + 1) T y τ j) y' :=
        (hAd j y' hy').sub (hBd j y' hy')
      have hfs : fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) T y τ j - IIIa.sepW ν ((μ : ℂ) + 1) T y τ j) y' =
          fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) T y τ j) y' -
            fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) T y τ j) y' :=
        fderiv_sub (hAd j y' hy') (hBd j y' hy')
      rw [e]
      refine (tcg_re_fderiv _ hd _).trans ?_
      rw [hfs]
      simp
    rw [Finset.sum_congr rfl (fun j _ => key j), ← Complex.re_sum, Finset.sum_sub_distrib, hA, hB]
    simp
  · intro τ' y' hyS hyax
    have hyS' : R * Real.sqrt (5 * ν / 6) < ϱ y' := hyS
    have hm : R * Real.sqrt (5 * ν / 6) < ϱ (meridPt y') := by
      rw [tcg_rho_meridPt]; exact hyS'
    have hI1 := sepIntegrableAt_of_source IIIa.sepKernelBounds sepPhiMeasurable sepGapPointwise
      sepGapMajorantIntegrable ν (μ : ℂ) _ P T hν hμc hr0 hP hS hM τ' (meridPt y') hm
    have hI2 := sepIntegrableAt_of_source IIIa.sepKernelBounds sepPhiMeasurable sepGapPointwise
      sepGapMajorantIntegrable ν ((μ : ℂ) + 1) _ P T hν hμc' hr0 hP hS hM τ' (meridPt y') hm
    exact sepX0_axi sepWEquivariance ν μ T hAx τ' y' hyax hI1 hI2

end UnforcedLeray.Short.PartIIIb.Concrete
