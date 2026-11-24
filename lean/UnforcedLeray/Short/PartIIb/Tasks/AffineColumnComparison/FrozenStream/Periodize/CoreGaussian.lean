import UnforcedLeray.Short.PartIIb.Sub.G4_2_3

/-!
# Part II-b, task `PartII-b:G4/2/3/2`: Gaussian bound for the smooth core

Source of record: `the November 2 reference manuscript`, lines 2349-2358.
Outside the closed ball of radius `ρ` the function `F - Hc` equals `F - M (x₁ - i x₂)^{-2}` on an
open set, so iterated derivatives agree there and the outside hypothesis applies. Inside the ball
the iterated derivatives are continuous, hence bounded on a compact set, and `exp(-κ|x|²)` is
bounded below there.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex

namespace UnforcedLeray.Short.IIb

theorem coreGaussian : UnforcedLeray.Short.IIb.CoreGaussian := by
  unfold UnforcedLeray.Short.IIb.CoreGaussian
  intro F Hc ρ M hF hHsm hρ hH hout j
  obtain ⟨C₁, κ, hκ, h₁⟩ := hout j
  have hGc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ × ℝ => F y - Hc y) := hF.sub hHsm
  have hcont : Continuous (fun x : ℝ × ℝ => iteratedFDeriv ℝ j (fun y : ℝ × ℝ => F y - Hc y) x) :=
    ContDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top) hGc
  have hcontn : Continuous (fun x : ℝ × ℝ => ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ => F y - Hc y) x‖) :=
    hcont.norm
  have hcontOn : ContinuousOn (fun x : ℝ × ℝ => ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ => F y - Hc y) x‖)
      (Metric.closedBall (0 : ℝ × ℝ) ρ) := hcontn.continuousOn
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_closedBall (0 : ℝ × ℝ) ρ) hcontOn
  refine ⟨max C₁ (max B 0 * Real.exp (κ * ρ ^ 2)), κ, hκ, fun x => ?_⟩
  by_cases hx : ρ ^ 2 < x.1 ^ 2 + x.2 ^ 2
  · have hU : IsOpen {x : ℝ × ℝ | ρ ^ 2 < x.1 ^ 2 + x.2 ^ 2} :=
      isOpen_lt continuous_const (by fun_prop)
    have hev : (fun y : ℝ × ℝ => F y - Hc y) =ᶠ[𝓝 x]
        (fun y : ℝ × ℝ => F y - M * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      rw [hH y hy]
    rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
    calc ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ => F y - M * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) x‖
        ≤ C₁ * Real.exp (-(κ * (x.1 ^ 2 + x.2 ^ 2))) := h₁ x hx
      _ ≤ max C₁ (max B 0 * Real.exp (κ * ρ ^ 2)) * Real.exp (-(κ * (x.1 ^ 2 + x.2 ^ 2))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · push_neg at hx
    have hmem : x ∈ Metric.closedBall (0 : ℝ × ℝ) ρ := by
      rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
      constructor <;> rw [Real.norm_eq_abs, abs_le] <;> constructor <;>
        nlinarith [sq_nonneg x.1, sq_nonneg x.2, sq_nonneg (x.1 + ρ), sq_nonneg (x.1 - ρ),
          sq_nonneg (x.2 + ρ), sq_nonneg (x.2 - ρ)]
    have hbound : ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ => F y - Hc y) x‖ ≤ B := by
      have := hB x hmem
      rwa [norm_norm] at this
    have hkey : Real.exp (κ * ρ ^ 2) * Real.exp (-(κ * (x.1 ^ 2 + x.2 ^ 2)))
        = Real.exp (κ * (ρ ^ 2 - (x.1 ^ 2 + x.2 ^ 2))) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp : 1 ≤ Real.exp (κ * (ρ ^ 2 - (x.1 ^ 2 + x.2 ^ 2))) :=
      Real.one_le_exp (by nlinarith)
    have h2 : max B 0 ≤ max B 0 * Real.exp (κ * ρ ^ 2) * Real.exp (-(κ * (x.1 ^ 2 + x.2 ^ 2))) := by
      calc max B 0 = max B 0 * 1 := (mul_one _).symm
        _ ≤ max B 0 * Real.exp (κ * (ρ ^ 2 - (x.1 ^ 2 + x.2 ^ 2))) :=
          mul_le_mul_of_nonneg_left hexp (le_max_right _ _)
        _ = max B 0 * Real.exp (κ * ρ ^ 2) * Real.exp (-(κ * (x.1 ^ 2 + x.2 ^ 2))) := by
          rw [mul_assoc, hkey]
    calc ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ => F y - Hc y) x‖
        ≤ B := hbound
      _ ≤ max B 0 := le_max_left _ _
      _ ≤ max B 0 * Real.exp (κ * ρ ^ 2) * Real.exp (-(κ * (x.1 ^ 2 + x.2 ^ 2))) := h2
      _ ≤ max C₁ (max B 0 * Real.exp (κ * ρ ^ 2)) * Real.exp (-(κ * (x.1 ^ 2 + x.2 ^ 2))) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

end UnforcedLeray.Short.IIb
