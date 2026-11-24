import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.GradX0Struct
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Defs

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem tcGradX0StructW : TCGradX0StructW := by
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

end
