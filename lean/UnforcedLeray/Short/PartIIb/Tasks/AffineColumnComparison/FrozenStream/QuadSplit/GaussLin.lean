import UnforcedLeray.Short.PartIIb.Sub.G4_2_2_1

/-!
# Part II-b, task `PartII-b:G4/2/2/2/1`: `GaussLin`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: linearity of `iteratedDeriv` at points `r > 0` (both summands are `ContDiffAt` there,
since `f` and `g` are smooth on the open set `(0,∞)`), the triangle inequality, and the
comparison `e^{-κ₁ r²} ≤ e^{-min(κ₁,κ₂) r²}` for `r ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

theorem gaussLin : UnforcedLeray.Short.IIb.GaussLin := by
  intro a b f g n hf hg hfG hgG j hj
  obtain ⟨C1, κ1, hκ1, h1⟩ := hfG j hj
  obtain ⟨C2, κ2, hκ2, h2⟩ := hgG j hj
  refine ⟨‖a‖ * C1 + ‖b‖ * C2, min κ1 κ2, lt_min hκ1 hκ2, fun r hr => ?_⟩
  have hr0 : (0 : ℝ) < r := by linarith
  have hfa : ContDiffAt ℝ j f r :=
    (hf.contDiffAt (Ioi_mem_nhds hr0)).of_le (by exact_mod_cast le_top)
  have hgb : ContDiffAt ℝ j g r :=
    (hg.contDiffAt (Ioi_mem_nhds hr0)).of_le (by exact_mod_cast le_top)
  have e : iteratedDeriv j (fun s => a * f s + b * g s) r
      = a * iteratedDeriv j f r + b * iteratedDeriv j g r := by
    have hA : ContDiffAt ℝ j (fun s => a * f s) r := contDiffAt_const.mul hfa
    have hB : ContDiffAt ℝ j (fun s => b * g s) r := contDiffAt_const.mul hgb
    rw [show (fun s => a * f s + b * g s) = (fun s => a * f s) + (fun s => b * g s) from rfl,
      iteratedDeriv_add hA hB, iteratedDeriv_const_mul a hfa, iteratedDeriv_const_mul b hgb]
  have hC1 : 0 ≤ C1 :=
    (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp (le_trans (norm_nonneg _) (h1 r hr))
  have hC2 : 0 ≤ C2 :=
    (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp (le_trans (norm_nonneg _) (h2 r hr))
  have hm1 : Real.exp (-(κ1 * r ^ 2)) ≤ Real.exp (-(min κ1 κ2 * r ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_left κ1 κ2) (sq_nonneg r)
    linarith
  have hm2 : Real.exp (-(κ2 * r ^ 2)) ≤ Real.exp (-(min κ1 κ2 * r ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_right κ1 κ2) (sq_nonneg r)
    linarith
  rw [e]
  calc ‖a * iteratedDeriv j f r + b * iteratedDeriv j g r‖
      ≤ ‖a * iteratedDeriv j f r‖ + ‖b * iteratedDeriv j g r‖ := norm_add_le _ _
    _ = ‖a‖ * ‖iteratedDeriv j f r‖ + ‖b‖ * ‖iteratedDeriv j g r‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ ‖a‖ * (C1 * Real.exp (-(κ1 * r ^ 2))) + ‖b‖ * (C2 * Real.exp (-(κ2 * r ^ 2))) :=
        add_le_add (mul_le_mul_of_nonneg_left (h1 r hr) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (h2 r hr) (norm_nonneg _))
    _ ≤ ‖a‖ * (C1 * Real.exp (-(min κ1 κ2 * r ^ 2))) +
          ‖b‖ * (C2 * Real.exp (-(min κ1 κ2 * r ^ 2))) :=
        add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm1 hC1) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm2 hC2) (norm_nonneg _))
    _ = (‖a‖ * C1 + ‖b‖ * C2) * Real.exp (-(min κ1 κ2 * r ^ 2)) := by ring

end UnforcedLeray.Short.IIb

end
