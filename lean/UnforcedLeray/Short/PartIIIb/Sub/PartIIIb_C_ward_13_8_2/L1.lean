import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2

/-!
# `PartIII-b:C/ward/13/8/2/1`: the standard cutoff family

Statement `CutoffFamily` from `Sub/PartIII-b_C_ward_13_8_2.lean` (source 117-118, 2641-2642).
Witness: `χ_R(y) = χ(R⁻¹ • y)` for a fixed smooth bump `χ` with radii `1` and `2`, and
`C = sup ‖fderiv χ‖`, which is finite because `fderiv χ` is continuous with compact support.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The fixed bump: `1` on `|y| ≤ 1`, `0` on `|y| ≥ 2`. -/
def cutoffBump : ContDiffBump (0 : UnforcedLeray.Space) :=
  ⟨1, 2, by norm_num, by norm_num⟩

theorem cutoffFamily : CutoffFamily := by
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : UnforcedLeray.Space => cutoffBump y) :=
    cutoffBump.contDiff
  have hcs : HasCompactSupport (fun y : UnforcedLeray.Space => cutoffBump y) :=
    cutoffBump.hasCompactSupport
  have hD : Continuous (fderiv ℝ (fun y : UnforcedLeray.Space => cutoffBump y)) :=
    hsm.continuous_fderiv (by simp)
  obtain ⟨C0, hC0⟩ := hD.bounded_above_of_compact_support (HasCompactSupport.fderiv (𝕜 := ℝ) hcs)
  refine ⟨fun R y => cutoffBump (R⁻¹ • y), C0, fun R hR => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · have hlin : ∀ R : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : UnforcedLeray.Space => R⁻¹ • y) :=
      fun R => contDiff_id.const_smul R⁻¹
    exact hsm.comp (hlin R)
  · intro y
    exact ⟨cutoffBump.nonneg, cutoffBump.le_one⟩
  · intro y hy
    show cutoffBump (R⁻¹ • y) = 1
    apply cutoffBump.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    show R⁻¹ * ‖y‖ ≤ 1
    rw [inv_mul_le_iff₀ hR, mul_one]
    exact hy
  · intro y hy
    show cutoffBump (R⁻¹ • y) = 0
    apply cutoffBump.zero_of_le_dist
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    show (2:ℝ) ≤ R⁻¹ * ‖y‖
    rw [inv_mul_eq_div, le_div_iff₀ hR]
    exact hy
  · intro y
    have hf : HasFDerivAt (fun z : UnforcedLeray.Space => cutoffBump z)
        (fderiv ℝ (fun z : UnforcedLeray.Space => cutoffBump z) (R⁻¹ • y)) (R⁻¹ • y) :=
      ((hsm.differentiable (by simp)) (R⁻¹ • y)).hasFDerivAt
    have hg : HasFDerivAt (fun z : UnforcedLeray.Space => R⁻¹ • z)
        (R⁻¹ • ContinuousLinearMap.id ℝ UnforcedLeray.Space) y :=
      (hasFDerivAt_id y).const_smul R⁻¹
    have hcomp := HasFDerivAt.comp y hf hg
    have hfd : fderiv ℝ (fun z : UnforcedLeray.Space => cutoffBump (R⁻¹ • z)) y
        = (fderiv ℝ (fun z : UnforcedLeray.Space => cutoffBump z) (R⁻¹ • y)).comp
            (R⁻¹ • ContinuousLinearMap.id ℝ UnforcedLeray.Space) := hcomp.fderiv
    show ‖fderiv ℝ (fun z : UnforcedLeray.Space => cutoffBump (R⁻¹ • z)) y‖ ≤ C0 / R
    rw [hfd]
    calc ‖(fderiv ℝ (fun z : UnforcedLeray.Space => cutoffBump z) (R⁻¹ • y)).comp
            (R⁻¹ • ContinuousLinearMap.id ℝ UnforcedLeray.Space)‖
        ≤ ‖fderiv ℝ (fun z : UnforcedLeray.Space => cutoffBump z) (R⁻¹ • y)‖ *
            ‖R⁻¹ • ContinuousLinearMap.id ℝ UnforcedLeray.Space‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C0 * (R⁻¹ * 1) := by
          apply mul_le_mul (hC0 _) _ (norm_nonneg _) (le_trans (norm_nonneg _) (hC0 (R⁻¹ • y)))
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
          exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_pos.mpr hR).le
      _ = C0 / R := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
