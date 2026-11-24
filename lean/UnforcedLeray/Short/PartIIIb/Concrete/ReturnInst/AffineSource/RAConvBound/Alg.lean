import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.ChartRuleGen

/-!
# `RAConvBound` helper: algebra of `physDivSym` (source 5045-5050)

Source of record: `the November 2 reference manuscript` (73 pages), 5045-5050.
Additivity of `physDivSym` in its first slot and the pointwise bound
`‖div(w⊗h + h⊗w)‖ ≤ 4δ(‖Dh‖ + ‖h‖)` for `‖w‖, ‖Dw‖ ≤ δ`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rac_physDivSym_sub (a b h : Space → Space) (y : Space) (ha : DifferentiableAt ℝ a y)
    (hb : DifferentiableAt ℝ b y) (hh : DifferentiableAt ℝ h y) :
    physDivSym a h y - physDivSym b h y = physDivSym (fun y' => a y' - b y') h y := by
  have hab : DifferentiableAt ℝ (fun y' => a y' - b y') y := ha.sub hb
  ext i
  simp only [physDivSym, PiLp.toLp_apply, PiLp.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h3 := pw4_sym_fderiv (fun y' => a y' - b y') h y hab hh i j (coordinateVector j)
  simp only [PiLp.sub_apply] at h3
  rw [pw4_sym_fderiv a h y ha hh i j _, pw4_sym_fderiv b h y hb hh i j _, h3, fderiv_fun_sub ha hb]
  simp only [ContinuousLinearMap.sub_apply, PiLp.sub_apply]
  ring

theorem rac_abs_div_le (f : Space → Space) (y : Space) :
    |Axi.divergence f y| ≤ 3 * ‖fderiv ℝ f y‖ := by
  unfold Axi.divergence
  calc |∑ i : Fin 3, (fderiv ℝ f y (coordinateVector i)) i|
      ≤ ∑ i : Fin 3, |(fderiv ℝ f y (coordinateVector i)) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, ‖fderiv ℝ f y‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc |(fderiv ℝ f y (coordinateVector i)) i|
            = ‖(fderiv ℝ f y (coordinateVector i)) i‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ f y (coordinateVector i)‖ := PiLp.norm_apply_le _ _
          _ ≤ ‖fderiv ℝ f y‖ * ‖coordinateVector i‖ := ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ f y‖ := by simp [coordinateVector]
    _ = 3 * ‖fderiv ℝ f y‖ := by simp

theorem rac_physDivSym_norm (w h : Space → Space) (y : Space) (hw : DifferentiableAt ℝ w y)
    (hh : DifferentiableAt ℝ h y) {δ : ℝ} (h1 : ‖w y‖ ≤ δ) (h2 : ‖fderiv ℝ w y‖ ≤ δ) :
    ‖physDivSym w h y‖ ≤ 4 * δ * (‖fderiv ℝ h y‖ + ‖h y‖) := by
  rw [crg_physDivSym_eq w h y hw hh]
  have hδ : 0 ≤ δ := (norm_nonneg _).trans h1
  have e1 : ‖Axi.advection w h y‖ ≤ ‖fderiv ℝ h y‖ * δ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
  have e2 : ‖Axi.advection h w y‖ ≤ δ * ‖h y‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  have e3 : ‖Axi.divergence w y • h y‖ ≤ 3 * δ * ‖h y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((rac_abs_div_le w y).trans (by linarith)) (norm_nonneg _)
  have e4 : ‖Axi.divergence h y • w y‖ ≤ 3 * ‖fderiv ℝ h y‖ * δ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (rac_abs_div_le h y) h1 (norm_nonneg _) (by positivity)
  calc _ ≤ ‖Axi.advection w h y‖ + ‖Axi.advection h w y‖ + ‖Axi.divergence w y • h y‖ +
        ‖Axi.divergence h y • w y‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := by nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete
