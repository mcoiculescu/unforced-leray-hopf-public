import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Int.Deriv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_1_HRep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE

/-!
# Half-plane bounds for `X₀` and its derivatives; the free equation

Source `the November 2 reference manuscript` 4171, 4181-4192, 4199.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcd_norm_cv (j : Fin 3) : ‖(UnforcedLeray.coordinateVector j : Space)‖ = 1 := by
  simp [UnforcedLeray.coordinateVector]

/-- `fderiv` of a directional derivative. -/
theorem tcd_fderiv_dir {f : Space → Space} {y : Space} (hf : ContDiffAt ℝ 2 f y) (v w : Space) :
    fderiv ℝ (fun y' => fderiv ℝ f y' v) y w = fderiv ℝ (fderiv ℝ f) y w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y := by
    have := hf.fderiv_right (m := 1) (by norm_num)
    exact this.differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem tcd_norm_hess {f : Space → Space} {y : Space} (hf : ContDiffAt ℝ 2 f y) :
    ‖fderiv ℝ (fderiv ℝ f) y‖ = ‖iteratedFDeriv ℝ 2 f y‖ := by
  have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 1) (f := f) (x := y)
  rw [norm_iteratedFDeriv_one] at h1
  exact h1

theorem tcd_physLap_norm {f : Space → Space} {y : Space} (hf : ContDiffAt ℝ 2 f y) :
    ‖physLap f y‖ ≤ 3 * ‖iteratedFDeriv ℝ 2 f y‖ := by
  unfold physLap
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ j : Fin 3, ‖physPd2 f j j y‖ ≤ ‖iteratedFDeriv ℝ 2 f y‖ := by
    intro j
    unfold physPd2 physPd
    rw [tcd_fderiv_dir hf]
    calc ‖fderiv ℝ (fderiv ℝ f) y (UnforcedLeray.coordinateVector j) (UnforcedLeray.coordinateVector j)‖
        ≤ ‖fderiv ℝ (fderiv ℝ f) y (UnforcedLeray.coordinateVector j)‖ *
            ‖(UnforcedLeray.coordinateVector j : Space)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) y‖ * ‖(UnforcedLeray.coordinateVector j : Space)‖ *
            ‖(UnforcedLeray.coordinateVector j : Space)‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ 2 f y‖ := by rw [tcd_norm_cv, tcd_norm_hess hf]; ring
  calc ∑ j : Fin 3, ‖physPd2 f j j y‖ ≤ ∑ _j : Fin 3, ‖iteratedFDeriv ℝ 2 f y‖ :=
        Finset.sum_le_sum (fun j _ => h1 j)
    _ = 3 * ‖iteratedFDeriv ℝ 2 f y‖ := by simp

theorem tcd_varrho {ρ z : ℝ} (hρ : 0 ≤ ρ) : ϱ (!₂[ρ, 0, z] : Space) = ρ := by
  unfold ϱ
  simp [Real.sqrt_sq hρ]

theorem tcd_norm_pt (ρ z : ℝ) (hρ : 0 ≤ ρ) : ‖(!₂[ρ, 0, z] : Space)‖ ≤ ρ + |z| := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs]
  rw [Real.sqrt_le_left (by positivity)]
  simp [sq_abs]
  nlinarith [abs_nonneg z, sq_abs z]

theorem tcd_rpow_split (D : ℝ) (hD : 0 < D) (j : ℕ) :
    D ^ (-(5 / 2 : ℝ) - j) = D ^ (-(3 / 2 : ℝ)) * (D⁻¹) ^ (1 + j) := by
  have h1 : D ^ (-(5 / 2 : ℝ) - j) = D ^ (-(3 / 2 : ℝ) + (-((1 + j : ℕ) : ℝ))) := by
    congr 1
    push_cast
    ring
  have h2 : D ^ (-((1 + j : ℕ) : ℝ)) = (D⁻¹) ^ (1 + j) := by
    rw [Real.rpow_neg hD.le, Real.rpow_natCast, inv_pow]
  rw [h1, Real.rpow_add hD, h2]

/-- ContDiffAt of `X₀`. -/
theorem tcd_X0_cd {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) {y : Space} (hy : rOut < ϱ y) :
    ContDiffAt ℝ 2 (sepX0 ν μ T τ) y := by
  have hm1 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm2 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hWa : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν (μ : ℂ) T z τ) {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν
      hm1 hr hP hT hM τ i)
  have hWb : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν ((μ : ℂ) + 1) T z τ)
      {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) rOut P T hν
      hm2 hr hP hT hM τ i)
  have : ContDiffOn ℝ 2 (sepX0 ν μ T τ) {y : Space | rOut < ϱ y} := by
    rw [sepX0_eq_reL]
    exact (reL.contDiff.comp_contDiffOn (hWa.sub hWb))
  exact this.contDiffAt (hU.mem_nhds hy)

/-- The free equation `D_{μ+1}X₀ = W_μ`. -/
theorem tcd_freeEq {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) {y : Space} (hy : rOut < ϱ y) :
    deriv (fun t => sepX0 ν μ T t y) τ =
      sepWre ν μ T τ y + (1 / 2 : ℝ) • fderiv ℝ (sepX0 ν μ T τ) y y +
        ν • physLap (sepX0 ν μ T τ) y - ((μ + 1) - 1 / 2) • sepX0 ν μ T τ y := by
  have h := sepX0FreeEq_of sepWHRep sepKerPDE sepX0Comb ν μ rOut P hν hμ hr hP T hT hM τ y hy
  unfold physDmu at h
  rw [← h]
  abel

end UnforcedLeray.Short.PartIIIb.Concrete

end
