import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalNormalizedMild

/-!
# Concrete diffusion clock in turnover coordinates

Identify the shifted free family in the normalized mild formula with the actual coefficient
`β(u)=(R-u)⁻¹` integrated across the finite block.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0123

/-- The backward Gaussian free family is exactly the exponential of the turnover diffusion clock. -/
theorem freeU_turnover_clock {R b₀ s t : ℝ} (hb₀ : 0 < b₀)
    (hs : 0 ≤ s) (hst : s ≤ t) (htt : t ≤ R - b₀) :
    freeU (t - R) (s - R) = expD (∫ u in s..t, (R - u)⁻¹) := by
  have hRts : 0 < R - t := by linarith [htt, hb₀]
  have hRss : 0 < R - s := by linarith [htt, hs, hb₀]
  have hclock : (∫ u in s..t, (R - u)⁻¹) =
      Real.log (R - s) - Real.log (R - t) := by
    calc
      (∫ u in s..t, (R - u)⁻¹) =
          ∫ v in R - t..R - s, v⁻¹ := by
            rw [intervalIntegral.integral_comp_sub_left (fun v : ℝ => v⁻¹) R]
      _ = Real.log ((R - s) / (R - t)) :=
            integral_inv_of_pos hRts hRss
      _ = Real.log (R - s) - Real.log (R - t) := by
            rw [Real.log_div hRss.ne' hRts.ne']
  have hlogs :
      Real.log (-(s - R)) - Real.log (-(t - R)) =
        Real.log (R - s) - Real.log (R - t) := by
    congr 2 <;> congr 1 <;> ring
  unfold freeU
  rw [hclock, ← hlogs]

/-- The normalized turnover free propagator is the explicit scalar gauge ratio times the concrete
Gaussian clock `expD(∫β)`. -/
theorem normalizedTurnoverFree_eq_gauge_clock {lam κ : ℂ} {R b₀ s t : ℝ}
    (hb₀ : 0 < b₀) (hs : 0 ≤ s) (hst : s ≤ t) (htt : t ≤ R - b₀) :
    normalizedTurnoverFree lam κ R t s =
      (gauge lam κ (R - t) * gaugeInv lam κ (R - s)) •
        expD (∫ u in s..t, (R - u)⁻¹) := by
  simp [normalizedTurnoverFree, freeU_turnover_clock hb₀ hs hst htt]

end UnforcedLeray.Cons.G3b
