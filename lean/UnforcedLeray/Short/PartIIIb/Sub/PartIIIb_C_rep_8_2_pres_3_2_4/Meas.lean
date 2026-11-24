import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_1

/-!
# Helpers for the measurability and axisymmetry leaves of `pres/3/2/{2,3,4}`

Source `the November 2 reference manuscript`,
lines 1205-1225, 2031, 2681-2688.  `axisZero f` is measurable when `f` is continuous off the axis;
`merPt` preserves `ϱ` and the third coordinate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem pf4_axisZero_measurable {f : ℝ → Space → ℝ}
    (h : ContinuousOn (fun x : ℝ × Space => f x.1 x.2) offAxisSet) :
    Measurable (axisZero f) := by
  classical
  set s : Set (ℝ × Space) := {x | x.2 ∈ axis} with hs
  have hsc : IsClosed s := isClosed_axis.preimage continuous_snd
  have hcompl : sᶜ = offAxisSet := rfl
  have e : axisZero f = s.piecewise (fun _ => (0 : ℝ)) (fun x => f x.1 x.2) := by
    funext x
    by_cases hx : x.2 ∈ axis
    · have : x ∈ s := hx
      simp [axisZero, hx, Set.piecewise, this]
    · have : x ∉ s := hx
      simp [axisZero, hx, Set.piecewise, this]
  rw [e]
  refine ContinuousOn.measurable_piecewise continuousOn_const ?_ hsc.measurableSet
  rw [hcompl]; exact h

theorem pf4_ϱ_merPt (y : Space) : ϱ (merPt y) = ϱ y := by
  have h0 : (merPt y) 0 = ϱ y := by simp [merPt]
  have h1 : (merPt y) 1 = 0 := by simp [merPt]
  unfold ϱ at *
  rw [h0, h1]
  simp only [ϱ] 
  rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq (Real.sqrt_nonneg _)]

theorem pf4_merPt_two (y : Space) : (merPt y) 2 = y 2 := by simp [merPt]

theorem pf4_merPt_of_mem_axis {y : Space} (hy : y ∈ axis) : merPt y = y := by
  have h0 : y 0 = 0 := hy.1
  have h1 : y 1 = 0 := hy.2
  have hr : ϱ y = 0 := (mem_axis_iff y).1 hy
  ext i
  fin_cases i <;> simp [merPt, hr, h0, h1]

theorem pf4_norm_eR_e3 {x : Space} (hx : x ∉ axis) (a b : ℝ) :
    ‖a • eR x + b • e3‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have hn : ‖eR x‖ = 1 := norm_eR hx
  have h3 : ‖(e3 : Space)‖ = 1 := by simp [e3, coordinateVector]
  rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right,
    inner_eR_e3, hn, h3]
  simp [Real.norm_eq_abs, sq_abs]

/-- The norm of a meridional combination `a e_r + b e₃` at `x` equals that at `merPt x`. -/
theorem pf4_norm_merid_eq (a b : ℝ) (x : Space) :
    ‖a • eR x + b • e3‖ = ‖a • eR (merPt x) + b • e3‖ := by
  by_cases hx : x ∈ axis
  · rw [pf4_merPt_of_mem_axis hx]
  · have hm := pf_merPt_not_mem_axis hx
    have h1 := pf4_norm_eR_e3 hx a b
    have h2 := pf4_norm_eR_e3 hm a b
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.trans h2.symm)

end UnforcedLeray.Short.PartIIIb.Concrete
