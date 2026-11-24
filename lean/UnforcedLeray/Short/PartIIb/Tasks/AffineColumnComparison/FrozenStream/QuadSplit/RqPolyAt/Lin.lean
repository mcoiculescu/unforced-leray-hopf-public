import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_2_1_5

/-!
# Part II-b, task `PartII-b:G4/2/2/1/5/2`: `PolyLin`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: linearity of `iteratedDeriv` at points `r > 0` (both summands are `ContDiffAt` there),
the triangle inequality, and the comparison `r^N₁ ≤ r^(N₁+N₂)` for `r ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

theorem polyLin : UnforcedLeray.Short.IIb.PolyLin := by
  intro a b f g n hf hg hF hG j hj
  obtain ⟨C1, N1, h1⟩ := hF j hj
  obtain ⟨C2, N2, h2⟩ := hG j hj
  refine ⟨‖a‖ * |C1| + ‖b‖ * |C2|, N1 + N2, fun r hr => ?_⟩
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
  have hp1 : ‖iteratedDeriv j f r‖ ≤ |C1| * r ^ (N1 + N2) :=
    (h1 r hr).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hr0.le _)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (by omega)) (abs_nonneg _)))
  have hp2 : ‖iteratedDeriv j g r‖ ≤ |C2| * r ^ (N1 + N2) :=
    (h2 r hr).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hr0.le _)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (by omega)) (abs_nonneg _)))
  rw [e]
  calc ‖a * iteratedDeriv j f r + b * iteratedDeriv j g r‖
      ≤ ‖a * iteratedDeriv j f r‖ + ‖b * iteratedDeriv j g r‖ := norm_add_le _ _
    _ = ‖a‖ * ‖iteratedDeriv j f r‖ + ‖b‖ * ‖iteratedDeriv j g r‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ ‖a‖ * (|C1| * r ^ (N1 + N2)) + ‖b‖ * (|C2| * r ^ (N1 + N2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hp1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hp2 (norm_nonneg _))
    _ = (‖a‖ * |C1| + ‖b‖ * |C2|) * r ^ (N1 + N2) := by ring

end UnforcedLeray.Short.IIb
