import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.
The bounds come from compact support: `ρ'` and `(θ')' ` are continuous with compact support.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- A continuous compactly supported real function is uniformly bounded by a nonnegative constant. -/
theorem cutProps_bdd (g : ℝ → ℝ) (hg : Continuous g) (hgcs : HasCompactSupport g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, |g y| ≤ K := by
  obtain ⟨K, hK⟩ := hg.bounded_above_of_compact_support hgcs
  refine ⟨max K 0, le_max_right _ _, fun y => ?_⟩
  rw [← Real.norm_eq_abs]
  exact le_trans (hK y) (le_max_left _ _)

theorem cutProps : UnforcedLeray.Short.IIb.CutProps := by
  have hρC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => cutBump y) := cutBump.contDiff
  have hρcs : HasCompactSupport (fun y : ℝ => cutBump y) := cutBump.hasCompactSupport
  have hcut_eq : cutθ = fun y => cutBump y * cutBump y := by
    funext y
    unfold cutθ
    ring
  have hcutC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cutθ := by
    rw [hcut_eq]
    exact hρC.mul hρC
  have hcutcs : HasCompactSupport cutθ := by
    rw [hcut_eq]
    exact hρcs.mul_right
  have hcutcs1 : HasCompactSupport (deriv cutθ) := hcutcs.deriv
  have hc1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv cutθ) := by
    have h := ContDiff.iterate_deriv 1 hcutC
    simpa using h
  have hcont1 : Continuous (deriv cutθ) := hcutC.continuous_deriv (by simp)
  have hcont2 : Continuous (deriv (deriv cutθ)) := hc1.continuous_deriv (by simp)
  have hdρ : Differentiable ℝ (fun y : ℝ => cutBump y) := hρC.differentiable (by simp)
  have hdcut : ∀ y : ℝ, deriv cutθ y = 2 * cutBump y * deriv (fun y : ℝ => cutBump y) y := by
    intro y
    rw [hcut_eq]
    have h : HasDerivAt (fun y : ℝ => cutBump y * cutBump y) _ y :=
      (hdρ y).hasDerivAt.mul (hdρ y).hasDerivAt
    rw [h.deriv]
    ring
  obtain ⟨K1, hK1nn, hK1⟩ :=
    cutProps_bdd _ (hρC.continuous_deriv (by simp)) hρcs.deriv
  obtain ⟨K2, hK2nn, hK2⟩ := cutProps_bdd _ hcont2 hcutcs1.deriv
  -- value at the centre
  have hb0 : cutBump 0 = 1 := cutBump.one_of_mem_closedBall (by norm_num [cutBump])
  have h0 : cutθ 0 = 1 := by
    unfold cutθ
    rw [hb0]
    norm_num
  have hrange : ∀ y : ℝ, 0 ≤ cutθ y ∧ cutθ y ≤ 1 := by
    intro y
    have h1 : 0 ≤ cutBump y := cutBump.nonneg
    have h2 : cutBump y ≤ 1 := cutBump.le_one
    unfold cutθ
    constructor
    · positivity
    · nlinarith
  have hzero : ∀ y : ℝ, 1 ≤ |y| → cutθ y = 0 := by
    intro y hy
    have hdist : cutBump.rOut ≤ dist y 0 := by
      show (1 : ℝ) ≤ dist y 0
      rw [Real.dist_eq, sub_zero]
      exact hy
    have h1 : cutBump y = 0 := cutBump.zero_of_le_dist hdist
    unfold cutθ
    rw [h1]
    norm_num
  refine ⟨hcutC, h0, hrange, hzero, 4 * K1 ^ 2 + K2, ?_, ?_⟩
  · positivity
  · intro y
    refine ⟨?_, ?_⟩
    · rw [hdcut y]
      have hcy : cutθ y = cutBump y * cutBump y := congrFun hcut_eq y
      rw [hcy]
      have hsq : (deriv (fun y : ℝ => cutBump y) y) ^ 2 ≤ K1 ^ 2 := by
        have h1 := hK1 y
        have h2 := sq_abs (deriv (fun y : ℝ => cutBump y) y)
        nlinarith [abs_nonneg (deriv (fun y : ℝ => cutBump y) y)]
      have hnn : 0 ≤ cutBump y * cutBump y := mul_self_nonneg _
      calc (2 * cutBump y * deriv (fun y : ℝ => cutBump y) y) ^ 2
          = 4 * (deriv (fun y : ℝ => cutBump y) y) ^ 2 * (cutBump y * cutBump y) := by ring
        _ ≤ 4 * K1 ^ 2 * (cutBump y * cutBump y) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn
        _ ≤ (4 * K1 ^ 2 + K2) * (cutBump y * cutBump y) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn
    · have h := hK2 y
      have h4 : 0 ≤ 4 * K1 ^ 2 := by positivity
      linarith

end UnforcedLeray.Short.IIb
