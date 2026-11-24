import UnforcedLeray.Infra.VolterraEvolution.Strip
import UnforcedLeray.Infra.VolterraEvolution.Beta

/-!
# The iterated (Gamma-function) bound for the Picard terms

The classical form of the Picard estimate for the square-root Volterra kernel:
on the strip, the `n`-th Picard term satisfies

`‖uₙ(τ)‖ ≤ M₀ ‖x‖ (C₀ β Γ(1/2))ⁿ (τ - s)^{n/2} / Γ(n/2 + 1)`,

proved by the Beta-function recursion `integral_kernel_mul_rpow`.  (The construction in
`Strip.lean` uses the geometric weighted bound instead; this file records the sharper
short-time decay of the individual terms.)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral Real

namespace UnforcedLeray.Infra.VolterraEvolution

namespace VolterraData

variable {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ X] (D : VolterraData 𝕜 X Y)

/-- **Iterated kernel bound.** `‖uₙ(τ)‖ ≤ M₀ ‖x‖ (C₀ β Γ(1/2))ⁿ (τ-s)^{n/2} / Γ(n/2+1)`. -/
theorem norm_picard_le_gamma (s : ℝ) (x : X) (n : ℕ) :
    ∀ τ ∈ Icc s (s + 1), ‖D.picard s x n τ‖ ≤
      D.M₀ * ‖x‖ * (D.C₀ * D.β * Gamma (1 / 2)) ^ n * (τ - s) ^ ((n : ℝ) / 2) /
        Gamma ((n : ℝ) / 2 + 1) := by
  induction n with
  | zero =>
    intro τ hτ
    simp only [Nat.cast_zero, zero_div, rpow_zero, zero_add, Gamma_one, pow_zero, mul_one,
      div_one, picard_zero]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (D.norm_S₀_le _ (by linarith [hτ.1]) (by linarith [hτ.2])) (norm_nonneg _))
  | succ n ih =>
    intro τ hτ
    set K := D.C₀ * D.β * Gamma (1 / 2) with hK
    have hΓ : 0 < Gamma ((n : ℝ) / 2 + 1) := Gamma_pos_of_pos (by positivity)
    set A := D.M₀ * ‖x‖ * K ^ n / Gamma ((n : ℝ) / 2 + 1) with hA
    have hK0 : 0 ≤ K := by
      have := D.C₀_nonneg; have := D.β_nonneg
      have : 0 ≤ Gamma (1 / 2 : ℝ) := Gamma_nonneg_of_nonneg (by norm_num)
      positivity
    have hA0 : 0 ≤ A := by have := D.M₀_nonneg; positivity
    have ih' : ∀ r ∈ Icc s (s + 1), ‖D.picard s x n r‖ ≤ A * (r - s) ^ ((n : ℝ) / 2) := by
      intro r hr
      refine (ih r hr).trans (le_of_eq ?_)
      rw [hA]
      ring
    have hcont : Continuous (fun r : ℝ => (r - s) ^ ((n : ℝ) / 2)) :=
      (continuous_id.sub continuous_const).rpow_const fun _ => Or.inr (by positivity)
    have hg : IntervalIntegrable (fun r => D.C₀ * D.β * A *
        ((τ - r) ^ (-(1 / 2 : ℝ)) * (r - s) ^ ((n : ℝ) / 2))) volume s τ :=
      ((intervalIntegrable_kernel τ s τ).mul_continuousOn hcont.continuousOn).const_mul _
    rw [picard_succ]
    refine (norm_integral_le_of_norm_le hτ.1 ?_ hg).trans (le_of_eq ?_)
    · filter_upwards [ae_ne_real τ] with r hrτ hr
      have hr' : r ∈ Ico s τ := ⟨hr.1.le, lt_of_le_of_ne hr.2 hrτ⟩
      refine (D.norm_integrand_le hτ.2 hr' _).trans ?_
      have hk : 0 ≤ (τ - r) ^ (-(1 / 2 : ℝ)) := rpow_nonneg (by linarith [hr'.2]) _
      calc D.C₀ * D.β * (τ - r) ^ (-(1 / 2 : ℝ)) * ‖D.picard s x n r‖
          ≤ D.C₀ * D.β * (τ - r) ^ (-(1 / 2 : ℝ)) * (A * (r - s) ^ ((n : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (ih' r ⟨hr'.1, hr'.2.le.trans hτ.2⟩)
              (mul_nonneg (mul_nonneg D.C₀_nonneg D.β_nonneg) hk)
        _ = D.C₀ * D.β * A * ((τ - r) ^ (-(1 / 2 : ℝ)) * (r - s) ^ ((n : ℝ) / 2)) := by ring
    · rw [intervalIntegral.integral_const_mul,
        integral_kernel_mul_rpow hτ.1 (by have : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
                                          linarith)]
      rw [Nat.cast_succ, show ((n : ℝ) + 1) / 2 = (n : ℝ) / 2 + 1 / 2 by ring,
        show ((n : ℝ) / 2 + 1 / 2) + 1 = (n : ℝ) / 2 + 1 + 1 / 2 by ring, hA, hK]
      field_simp
      ring

end VolterraData

end UnforcedLeray.Infra.VolterraEvolution
