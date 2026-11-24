import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integral Gronwall to zero (helper for `PartI:C07/1/1/1`, `fullMildUnique`)

A continuous nonnegative `D` on `[a, c]` with `D θ ≤ K ∫_θ^c D` for all `θ ∈ [a, c]` satisfies
`D θ ≤ 0` there. Proof: iterate the inequality, obtaining
`D θ ≤ M K^n (c - θ)^n / n!` for every `n`, and let `n → ∞`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.PartI.FullMildUniqueHelp

/-- Gronwall to zero for an integral inequality on `[a, c]`. -/
theorem gronwall_le_zero {D : ℝ → ℝ} {a c K : ℝ} (hK : 0 ≤ K)
    (hD : ContinuousOn D (Icc a c)) (hnn : ∀ s ∈ Icc a c, 0 ≤ D s)
    (hle : ∀ θ ∈ Icc a c, D θ ≤ K * ∫ s in θ..c, D s) :
    ∀ θ ∈ Icc a c, D θ ≤ 0 := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  have hM' : ∀ x ∈ Icc a c, D x ≤ M := fun x hx => by
    have h := hM x hx
    rw [Real.norm_of_nonneg (hnn x hx)] at h
    exact h
  have hII : ∀ θ ∈ Icc a c, IntervalIntegrable D volume θ c := by
    intro θ hθ
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hθ.2]
    exact hD.mono (Icc_subset_Icc hθ.1 le_rfl)
  have key : ∀ n : ℕ, ∀ θ ∈ Icc a c,
      D θ ≤ M * K ^ n / (Nat.factorial n : ℝ) * (c - θ) ^ n := by
    intro n
    induction n with
    | zero =>
      intro θ hθ
      simpa using hM' θ hθ
    | succ n ih =>
      intro θ hθ
      have h1 : ∫ s in θ..c, D s ≤ ∫ s in θ..c, M * K ^ n / (Nat.factorial n : ℝ) * (c - s) ^ n := by
        apply intervalIntegral.integral_mono_on hθ.2 (hII θ hθ)
        · apply Continuous.intervalIntegrable
          fun_prop
        · intro s hs
          exact ih s ⟨hθ.1.trans hs.1, hs.2⟩
      have h2 : ∫ s in θ..c, M * K ^ n / (Nat.factorial n : ℝ) * (c - s) ^ n
          = M * K ^ n / (Nat.factorial n : ℝ) * ((c - θ) ^ (n + 1) / ((n : ℝ) + 1)) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        have h3 := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ n) (a := θ) (b := c) c
        rw [h3]
        simp [integral_pow]
      have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      calc D θ ≤ K * ∫ s in θ..c, D s := hle θ hθ
        _ ≤ K * ∫ s in θ..c, M * K ^ n / (Nat.factorial n : ℝ) * (c - s) ^ n :=
          mul_le_mul_of_nonneg_left h1 hK
        _ = K * (M * K ^ n / (Nat.factorial n : ℝ) * ((c - θ) ^ (n + 1) / ((n : ℝ) + 1))) := by
          rw [h2]
        _ = M * K ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) * (c - θ) ^ (n + 1) := by
          rw [Nat.factorial_succ]
          push_cast
          field_simp
          ring
  intro θ hθ
  have hlim : Tendsto (fun n : ℕ => M * ((K * (c - θ)) ^ n / (Nat.factorial n : ℝ)))
      atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (K * (c - θ))).const_mul M
  have hev : ∀ n : ℕ, D θ ≤ M * ((K * (c - θ)) ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    refine (key n θ hθ).trans (le_of_eq ?_)
    rw [mul_pow]
    ring
  exact ge_of_tendsto hlim (Eventually.of_forall hev)

end UnforcedLeray.Short.PartI.FullMildUniqueHelp
