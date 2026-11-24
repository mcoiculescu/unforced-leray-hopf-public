import UnforcedLeray.Short.PartI.Sub.T02_2_3

/-!
# Part I, task `PartI:T02/2/3`, leaf `PbGradToGrowth`: linear growth from bounded partials

Source of record: `the November 2 reference manuscript`, lines 276-288 and 447.

Target: `pbGradToGrowth : PbGradToGrowth` (the definition is in `Sub/T02_2_3.lean`).  For a
`C¹` `c`-periodic `q` on the plane with bounded partial derivatives (`|∂_q q|, |∂_η q| ≤ L`),
`|q z| ≤ C (1 + |z.2|)` for all `z`.

Proof.  Periodicity moves the first coordinate of `z` into `[0, c)`
(`Function.Periodic.exists_mem_Ico₀`).  On the compact set `[0, c]` the function `y ↦ q (y, 0)` is
bounded.  The mean value inequality along each vertical line gives `|q (y, η) - q (y, 0)| ≤ |L| |η|`
(`pbGG_vertical`).  Combining these gives the linear bound with `C = |Q₀| + |L|`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- Vertical Lipschitz bound.  If `|∂_η q| ≤ L` everywhere, then `|q (y, η) - q (y, 0)| ≤ |L| |η|`,
by the mean value inequality on the segment between `0` and `η`. -/
theorem pbGG_vertical {q : Plane → ℝ} (hdiff : Differentiable ℝ q) {L : ℝ}
    (hL : ∀ z : Plane, |Cyl.partialEta q z| ≤ L) (y η : ℝ) :
    |q (y, η) - q (y, 0)| ≤ |L| * |η| := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s => q (y, s)) (Cyl.partialEta q (y, t)) t :=
    fun t => Cyl.hasDerivAt_sliceEta hdiff y t
  have hb : ∀ t : ℝ, ‖Cyl.partialEta q (y, t)‖ ≤ |L| := fun t => by
    rw [Real.norm_eq_abs]
    exact (hL (y, t)).trans (le_abs_self L)
  rcases le_total 0 η with hη | hη
  · have key : ‖q (y, η) - q (y, 0)‖ ≤ |L| * (η - 0) :=
      norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := η)
        (f := fun s => q (y, s)) (f' := fun t => Cyl.partialEta q (y, t)) (C := |L|)
        (fun x _ => (hd x).hasDerivWithinAt) (fun x _ => hb x) η ⟨hη, le_rfl⟩
    rw [Real.norm_eq_abs, sub_zero] at key
    rw [abs_of_nonneg hη]
    exact key
  · have key : ‖q (y, 0) - q (y, η)‖ ≤ |L| * (0 - η) :=
      norm_image_sub_le_of_norm_deriv_le_segment' (a := η) (b := 0)
        (f := fun s => q (y, s)) (f' := fun t => Cyl.partialEta q (y, t)) (C := |L|)
        (fun x _ => (hd x).hasDerivWithinAt) (fun x _ => hb x) 0 ⟨hη, le_rfl⟩
    have key' : |q (y, η) - q (y, 0)| ≤ |L| * (0 - η) := by
      rw [← Real.norm_eq_abs, norm_sub_rev]
      exact key
    rw [abs_of_nonpos hη]
    linarith [key']

theorem pbGradToGrowth : PbGradToGrowth := by
  intro c q hc hq hper hLex
  obtain ⟨L, hL⟩ := hLex
  have hdiff : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hcont0 : Continuous (fun y : ℝ => q (y, (0 : ℝ))) :=
    hq.continuous.comp (continuous_id.prodMk continuous_const)
  have hcontOn : ContinuousOn (fun y : ℝ => q (y, (0 : ℝ))) (Icc 0 c) :=
    hcont0.continuousOn
  obtain ⟨Q0, hQ0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := c)).exists_bound_of_continuousOn hcontOn
  refine ⟨|Q0| + |L|, fun z => ?_⟩
  obtain ⟨x, η⟩ := z
  obtain ⟨y, hy, hxy⟩ := (hper.slice η).exists_mem_Ico₀ hc x
  have hxy' : q (x, η) = q (y, η) := hxy
  have hyI : y ∈ Icc (0 : ℝ) c := Ico_subset_Icc_self hy
  have hQy : |q (y, 0)| ≤ Q0 := by
    have := hQ0 y hyI
    simpa [Real.norm_eq_abs] using this
  have hsl : |q (y, η) - q (y, 0)| ≤ |L| * |η| :=
    pbGG_vertical hdiff (fun w => (hL w).2) y η
  show |q (x, η)| ≤ (|Q0| + |L|) * (1 + |η|)
  rw [hxy']
  have htri : |q (y, η)| ≤ |q (y, 0)| + |q (y, η) - q (y, 0)| := by
    have h := abs_add_le (q (y, 0)) (q (y, η) - q (y, 0))
    have e : q (y, 0) + (q (y, η) - q (y, 0)) = q (y, η) := by ring
    rw [e] at h
    exact h
  have hL0 : 0 ≤ |L| := abs_nonneg L
  have hQ0' : Q0 ≤ |Q0| := le_abs_self Q0
  have hQη : 0 ≤ |Q0| * |η| := mul_nonneg (abs_nonneg Q0) (abs_nonneg η)
  have hLη : 0 ≤ |L| * |η| := mul_nonneg hL0 (abs_nonneg η)
  nlinarith [htri, hQy, hsl, hQ0', hL0, hQη, hLη]

end UnforcedLeray.Short.PartI
