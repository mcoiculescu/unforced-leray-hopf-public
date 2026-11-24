import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Leibniz.Prod

/-!
# The stream cutoff as `𝒞_y Z = c(ϱ) Z + F(ϱ) ψ_Z` (`TCLeibniz` leaves)

Source `the November 2 reference manuscript` 4180-4186, 3700-3712.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcle_wsc_eq (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) :
    wardStreamCut ν R χy Z τ y =
      tcC0 ν R χy (ϱ y) • Z τ y + tcF0 ν R χy (ϱ y) • psiFld Z τ y := by
  unfold wardStreamCut psiFld tcC0 tcF0 age
  rw [mul_smul]

theorem tcle_inner_smooth (ν R : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ 2 (fun r : ℝ => ν * (R ^ 2 / r ^ 2)) r :=
  contDiffAt_const.mul (contDiffAt_const.div (contDiffAt_id.pow 2) (pow_ne_zero 2 hr))

theorem tcle_c0_smooth {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) (ν R : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ 2 (tcC0 ν R χy) r := by
  have h2 : ContDiff ℝ 2 χy := hχ.smooth.of_le (by first | exact WithTop.coe_le_coe.2 le_top | simp | norm_num)
  exact h2.contDiffAt.comp r (tcle_inner_smooth ν R hr)

theorem tcle_f0_smooth {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) (ν R : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ 2 (tcF0 ν R χy) r := by
  have h1 : ContDiff ℝ 2 (deriv χy) :=
    ((contDiff_infty_iff_deriv.mp hχ.smooth).2).of_le (by first | exact WithTop.coe_le_coe.2 le_top | simp | norm_num)
  have a : ContDiffAt ℝ 2 (fun r : ℝ => deriv χy (ν * (R ^ 2 / r ^ 2))) r :=
    h1.contDiffAt.comp r (tcle_inner_smooth ν R hr)
  have b : ContDiffAt ℝ 2 (fun r : ℝ => -2 * ν * R ^ 2 / r ^ 3) r :=
    contDiffAt_const.div (contDiffAt_id.pow 3) (pow_ne_zero 3 hr)
  exact (a.mul b).div contDiffAt_id hr


theorem tcle_ru_apply (y : Space) (j : Fin 3) :
    radialUnit y j = if j = 2 then 0 else (y j) / ϱ y := by
  fin_cases j <;> simp [radialUnit, div_eq_inv_mul]

theorem tcle_grad_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → ℝ)
    {y : Space} (h : 0 < ϱ y) (hg : DifferentiableAt ℝ g (ϱ y)) (L : Space →L[ℝ] E) :
    ∑ j : Fin 3, fderiv ℝ (fun y' => g (ϱ y')) y (coordinateVector j) • L (coordinateVector j) =
      deriv g (ϱ y) • L (radialUnit y) := by
  have hj : ∀ j : Fin 3, fderiv ℝ (fun y' => g (ϱ y')) y (coordinateVector j) =
      deriv g (ϱ y) * radialUnit y j := by
    intro j
    rw [tcle_fderiv_comp h hg, tcle_ru_apply]
    fin_cases j <;> simp [coordinateVector] <;> ring
  have hru : radialUnit y = ∑ j : Fin 3, radialUnit y j • (coordinateVector j : Space) := by
    ext i
    fin_cases i <;> simp [coordinateVector, Fin.sum_univ_three]
  conv_rhs => rw [hru]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hj, map_smul, mul_smul]

end UnforcedLeray.Short.PartIIIb.Concrete
