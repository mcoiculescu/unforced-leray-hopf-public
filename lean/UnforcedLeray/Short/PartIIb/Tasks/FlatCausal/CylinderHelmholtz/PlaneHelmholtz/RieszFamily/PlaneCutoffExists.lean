import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs

/-!
# Smooth cutoffs on the plane with gradient of order `1/R`

Source of record: `the November 2 reference manuscript`, line 1670 (the planar
projection `P_0 = I - ∇Δ⁻¹ div`) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory, Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8.

Fix a smooth bump `φ` on `Pl` with `φ = 1` on `‖x‖ ≤ 1`, `φ = 0` on `‖x‖ ≥ 2`, and `0 ≤ φ ≤ 1`
(a `ContDiffBump` with `rIn = 1`, `rOut = 2`).  The family `χ_R(x) = φ(R⁻¹ • x)` satisfies
`χ_R = 1` on `‖x‖ ≤ R`, `χ_R = 0` on `‖x‖ ≥ 2R`, and `‖∇χ_R‖ ≤ M / R` by the chain rule,
with `M` a bound for `‖Dφ‖` (finite since `Dφ` is continuous with compact support).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/26`.** Smooth cutoffs `χ_R` with `|∇χ_R| ≤ M / R` exist. -/
theorem planeCutoffExists : PlaneCutoffExists := by
  let φ : ContDiffBump (0 : Pl) :=
    { rIn := 1, rOut := 2, rIn_pos := one_pos, rIn_lt_rOut := by norm_num }
  have hφC : ContDiff ℝ ∞ φ := φ.contDiff
  have hdφC : Continuous (fderiv ℝ φ) := hφC.continuous_fderiv (by simp)
  obtain ⟨M0, hM0⟩ := hdφC.bounded_above_of_compact_support
    (φ.hasCompactSupport.fderiv (𝕜 := ℝ))
  unfold PlaneCutoffExists IsCutoffFamily
  refine ⟨fun R x => φ (R⁻¹ • x), ?_, ?_, ?_, ?_, M0, ?_⟩
  · intro R hR
    have hRpos : 0 < R := by linarith
    constructor
    · exact hφC.comp (contDiff_id.const_smul R⁻¹)
    · apply HasCompactSupport.intro (isCompact_closedBall (0 : Pl) (2 * R))
      intro x hx
      have hx' : 2 * R < ‖x‖ := lt_of_not_ge (fun h => hx (mem_closedBall_zero_iff.2 h))
      refine φ.zero_of_le_dist ?_
      show (2 : ℝ) ≤ dist (R⁻¹ • x) 0
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hRpos.le)]
      calc (2 : ℝ) = R⁻¹ * (2 * R) := by field_simp
        _ ≤ R⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left hx'.le (inv_nonneg.2 hRpos.le)
  · intro R x
    exact ⟨φ.nonneg, φ.le_one⟩
  · intro R x hR hx
    have hRpos : 0 < R := by linarith
    show φ (R⁻¹ • x) = 1
    apply φ.one_of_mem_closedBall
    show R⁻¹ • x ∈ Metric.closedBall (0 : Pl) 1
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hRpos.le)]
    calc R⁻¹ * ‖x‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hRpos.le)
      _ = 1 := inv_mul_cancel₀ hRpos.ne'
  · intro R x hR hx
    have hRpos : 0 < R := by linarith
    show φ (R⁻¹ • x) = 0
    refine φ.zero_of_le_dist ?_
    show (2 : ℝ) ≤ dist (R⁻¹ • x) 0
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hRpos.le)]
    calc (2 : ℝ) = R⁻¹ * (2 * R) := by field_simp
      _ ≤ R⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hRpos.le)
  · intro R x hR
    have hRpos : 0 < R := by linarith
    have hinv : (0 : ℝ) ≤ R⁻¹ := inv_nonneg.2 hRpos.le
    have hφd : HasFDerivAt φ (fderiv ℝ φ (R⁻¹ • x)) (R⁻¹ • x) :=
      ((hφC.differentiable (by simp)) (R⁻¹ • x)).hasFDerivAt
    have hl : HasFDerivAt (fun y : Pl => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ Pl) x :=
      (ContinuousLinearMap.id ℝ Pl).hasFDerivAt.const_smul R⁻¹
    have hcomp := hφd.comp x hl
    have hfd : fderiv ℝ (fun x => φ (R⁻¹ • x)) x =
        (fderiv ℝ φ (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ Pl) := hcomp.fderiv
    have hid : ‖R⁻¹ • ContinuousLinearMap.id ℝ Pl‖ ≤ R⁻¹ := by
      rw [norm_smul, Real.norm_of_nonneg hinv]
      have h1 : ‖ContinuousLinearMap.id ℝ Pl‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      calc R⁻¹ * ‖ContinuousLinearMap.id ℝ Pl‖ ≤ R⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 hinv
        _ = R⁻¹ := mul_one _
    rw [hfd]
    calc ‖(fderiv ℝ φ (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ Pl)‖
        ≤ ‖fderiv ℝ φ (R⁻¹ • x)‖ * ‖R⁻¹ • ContinuousLinearMap.id ℝ Pl‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M0 * R⁻¹ :=
          mul_le_mul (hM0 (R⁻¹ • x)) hid (norm_nonneg _) (le_trans (norm_nonneg _) (hM0 (R⁻¹ • x)))
      _ = M0 / R := by rw [div_eq_mul_inv]

end UnforcedLeray.Short.IIb.PlaneRiesz
