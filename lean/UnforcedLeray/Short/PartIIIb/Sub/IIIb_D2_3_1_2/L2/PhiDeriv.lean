import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2

/-!
# Directional derivative of the `sepW` integrand (`PartIII-b:IIIb-D2/3/1/2/2`)

Source `the November 2 reference manuscript` 3611-3617.
`D_y sepPhi(l,z,·)(e_i) = -2 l^{2μ+2} ∑_{jk} ∂_i[∂_kK_ij](y - lz) T_jk`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem sepPhi_fderiv_apply (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (i : Fin 3) (l : ℝ) (z y : Space) (hν : 0 < ν) (hl : l ∈ Ioo (0 : ℝ) 1) :
    fderiv ℝ (sepPhi ν μ T τ i (l, z)) y (coordinateVector i) =
      -2 * (l : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') x
          (coordinateVector k)) (y - l • z) (coordinateVector i) : ℝ) : ℂ) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) := by
  have ht : 0 < ν * (1 - l ^ 2) := by
    have := hl.1; have := hl.2; nlinarith [mul_pos hν (sub_pos.2 (show l ^ 2 < 1 by nlinarith))]
  have hg : ∀ j k : Fin 3, ContDiff ℝ 2 (fun x : Space =>
      fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') x (coordinateVector k)) :=
    fun j k => ((heatLerayKSmooth _ ht i j).fderiv_right (by norm_num)).clm_apply contDiff_const
  have hH : ∀ j k : Fin 3, HasFDerivAt (fun y' : Space =>
      ((fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') (y' - l • z)
        (coordinateVector k) : ℝ) : ℂ) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))
      (((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) • (Complex.ofRealCLM.comp (fderiv ℝ (fun x : Space =>
        fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') x (coordinateVector k))
          (y - l • z)))) y := by
    intro j k
    have h1 : HasFDerivAt (fun y' : Space => y' - l • z) (ContinuousLinearMap.id ℝ Space) y :=
      (hasFDerivAt_id y).sub_const (l • z)
    have h2 := ((hg j k).differentiable (by norm_num) (y - l • z)).hasFDerivAt.comp y h1
    have h3 := Complex.ofRealCLM.hasFDerivAt.comp y h2
    have h4 := h3.mul_const ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)
    refine h4.congr_fderiv ?_
    ext v
    simp [mul_comm]
  have hS : HasFDerivAt (fun y' : Space => ∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') (y' - l • z)
        (coordinateVector k) : ℝ) : ℂ) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))
      (∑ j : Fin 3, ∑ k : Fin 3,
        (((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) • (Complex.ofRealCLM.comp (fderiv ℝ
          (fun x : Space => fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') x
            (coordinateVector k)) (y - l • z))))) y :=
    HasFDerivAt.fun_sum fun j _ => HasFDerivAt.fun_sum fun k _ => hH j k
  have hF := hS.const_mul (-2 * (l : ℂ) ^ (2 * μ + 2))
  unfold sepPhi
  simp only
  rw [hF.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
