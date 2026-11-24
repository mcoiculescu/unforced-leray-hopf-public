import UnforcedLeray.Short.PartIIb.Sub.T22_4
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Leaf `PartII-b:T22/4/4` (`dbCutoff`): the family of `η`-cut-offs.

Source: `the November 2 reference manuscript` lines 2103-2104 ("smoothing").
`χ_n(t) = cutF (n+1) t = ψ(t / (n+1))` with `ψ` the fixed bump: `1` on `[-1,1]`, supported in
`(-2, 2)`, `0 ≤ ψ ≤ 1`. The derivative is `ψ'(t/(n+1)) / (n+1)`, bounded by `K/(n+1)` with
`K = sup |ψ'|` (compact support of `ψ'`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

namespace DbCutoffAux

/-- The fixed bump: `1` on `[-1, 1]`, supported in `(-2, 2)`. -/
def cutBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cut-off `χ_R(η) = ψ(η / R)`. -/
def cutF (R η : ℝ) : ℝ := cutBump (R⁻¹ * η)

/-- The `η`-derivative of `cutF R`. -/
def cutD (R η : ℝ) : ℝ := R⁻¹ * deriv (fun x : ℝ => cutBump x) (R⁻¹ * η)

theorem cutF_contDiff (R : ℝ) : ContDiff ℝ ∞ (fun η : ℝ => cutF R η) := by
  have h : ContDiff ℝ ∞ (fun η : ℝ => R⁻¹ * η) := contDiff_const.mul contDiff_id
  exact cutBump.contDiff.comp h

theorem cutF_nonneg (R η : ℝ) : 0 ≤ cutF R η := cutBump.nonneg

theorem cutF_le_one (R η : ℝ) : cutF R η ≤ 1 := cutBump.le_one

theorem cutF_eq_one {R η : ℝ} (hR : 0 < R) (h : |η| ≤ R) : cutF R η = 1 := by
  unfold cutF
  apply cutBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_mul,
    abs_of_pos (inv_pos.2 hR), inv_mul_le_iff₀ hR]
  have h1 : (cutBump).rIn = 1 := rfl
  rw [h1]
  linarith

theorem cutF_eq_zero {R η : ℝ} (hR : 0 < R) (h : 2 * R ≤ |η|) : cutF R η = 0 := by
  unfold cutF
  apply cutBump.zero_of_le_dist
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (inv_pos.2 hR), le_inv_mul_iff₀ hR]
  have h2 : (cutBump).rOut = 2 := rfl
  rw [h2]
  linarith

theorem hasDerivAt_cutF (R η : ℝ) : HasDerivAt (fun x : ℝ => cutF R x) (cutD R η) η := by
  have hcb : ContDiff ℝ ∞ (fun x : ℝ => cutBump x) := cutBump.contDiff
  have h1 : HasDerivAt (fun x : ℝ => cutBump x)
      (deriv (fun x : ℝ => cutBump x) (R⁻¹ * η)) (R⁻¹ * η) :=
    ((hcb.differentiable (by simp)) (R⁻¹ * η)).hasDerivAt
  have h2 : HasDerivAt (fun x : ℝ => R⁻¹ * x) R⁻¹ η := by
    simpa using (hasDerivAt_id η).const_mul R⁻¹
  have h3 := h1.comp η h2
  have e : cutD R η = deriv (fun x : ℝ => cutBump x) (R⁻¹ * η) * R⁻¹ := by
    unfold cutD
    ring
  rw [e]
  exact h3

theorem continuous_deriv_cutBump : Continuous (deriv (fun x : ℝ => cutBump x)) := by
  have hcb : ContDiff ℝ ∞ (fun x : ℝ => cutBump x) := cutBump.contDiff
  exact hcb.continuous_deriv (by exact_mod_cast le_top)

theorem exists_cutD_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R η : ℝ, 0 < R → |cutD R η| ≤ K * (1 / R) := by
  have hcs : HasCompactSupport (deriv (fun x : ℝ => cutBump x)) :=
    cutBump.hasCompactSupport.deriv
  obtain ⟨K, hK⟩ := continuous_deriv_cutBump.bounded_above_of_compact_support hcs
  refine ⟨max K 0, le_max_right _ _, fun R η hR => ?_⟩
  have hpos : 0 < R⁻¹ := inv_pos.2 hR
  have hb : |deriv (fun x : ℝ => cutBump x) (R⁻¹ * η)| ≤ max K 0 := by
    have := hK (R⁻¹ * η)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  unfold cutD
  rw [one_div, abs_mul, abs_of_pos hpos, mul_comm (max K 0)]
  exact mul_le_mul_of_nonneg_left hb hpos.le

end DbCutoffAux

open DbCutoffAux in
theorem dbCutoff : UnforcedLeray.Short.IIb.DbCutoff := by
  refine ⟨fun n => cutF ((n : ℝ) + 1), ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact cutF_contDiff _
  · intro n
    refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * ((n : ℝ) + 1)))
      (b := 2 * ((n : ℝ) + 1))) (fun x hx => ?_)
    refine cutF_eq_zero (R := (n : ℝ) + 1) (by positivity) ?_
    by_contra hlt
    push Not at hlt
    exact hx (Set.mem_Icc.mpr (abs_le.mp hlt.le))
  · intro n t
    exact ⟨cutF_nonneg _ _, cutF_le_one _ _⟩
  · intro n t ht
    refine cutF_eq_one (R := (n : ℝ) + 1) (by positivity) ?_
    obtain ⟨h1, h2⟩ := ht
    rw [abs_le]
    constructor <;> linarith
  · obtain ⟨K, _, hK⟩ := exists_cutD_bound
    refine ⟨K, fun n t => ?_⟩
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hd : deriv (fun η : ℝ => cutF ((n : ℝ) + 1) η) t = cutD ((n : ℝ) + 1) t :=
      (hasDerivAt_cutF _ t).deriv
    show |deriv (fun η : ℝ => cutF ((n : ℝ) + 1) η) t| ≤ K / ((n : ℝ) + 1)
    rw [hd]
    have h := hK ((n : ℝ) + 1) t hR
    rw [mul_one_div] at h
    exact h

end UnforcedLeray.Short.IIb
