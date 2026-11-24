import UnforcedLeray.Units.B0224
import UnforcedLeray.Units.B0223.Lift

/-!
# Strong continuity at `0` of `T₀`, reduced to dilation and heat strong continuity on `H`

Source `the November 2 reference manuscript` 1650-1656.

`T₀(s) = H_{θ_s} ∘ D_{e^{-s}}` (`UnforcedLeray.B0224.T0`, a definitional composition), and both
factors are contractions on `H` (`norm_heatH_le`, `norm_dilH_le`). Hence
`‖T₀(s)g - g‖ ≤ ‖D_{e^{-s}}g - g‖ + ‖H_{θ_s}g - g‖`, and the target follows from two strong
continuity facts on `H` which are the remaining analytic inputs (see the hypotheses `hD`, `hH`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- Reduction: strong continuity of `T₀` at `0` from strong continuity of the age dilation
at `s = 0` (`hD`) and of the age-dependent heat `H_{θ_s}` at `s = 0` (`hH`). -/
theorem t0_strong_cont_zero_of
    (hD : ∀ (c : ℝ) (g : HSpace c MeridC),
      Tendsto (fun s : ℝ => UnforcedLeray.B0224.dilH (Real.exp_pos (-s)) g) (𝓝[≥] 0) (𝓝 g))
    (hH : ∀ (c ν : ℝ) (hc : 0 < c) (g : HSpace c MeridC),
      Tendsto (fun s : ℝ =>
        UnforcedLeray.B0224.heatH hc (UnforcedLeray.B0224.measurable_heatTime ν s) g)
        (𝓝[≥] 0) (𝓝 g)) :
    ∀ (c ν : ℝ) (hc : 0 < c) (g : HSpace c MeridC),
      Tendsto (fun s : ℝ => UnforcedLeray.B0224.T0 hc ν s g) (𝓝[≥] 0) (𝓝 g) := by
  intro c ν hc g
  have key : ∀ s : ℝ, ‖UnforcedLeray.B0224.T0 hc ν s g - g‖ ≤
      ‖UnforcedLeray.B0224.dilH (Real.exp_pos (-s)) g - g‖ +
        ‖UnforcedLeray.B0224.heatH hc (UnforcedLeray.B0224.measurable_heatTime ν s) g - g‖ := by
    intro s
    set h : HSpace c MeridC := UnforcedLeray.B0224.dilH (Real.exp_pos (-s)) g with hh
    set H : HSpace c MeridC →L[ℝ] HSpace c MeridC :=
      UnforcedLeray.B0224.heatH hc (UnforcedLeray.B0224.measurable_heatTime ν s) with hH'
    have e1 : UnforcedLeray.B0224.T0 hc ν s g - g = H (h - g) + (H g - g) := by
      show H h - g = _
      rw [map_sub]
      abel
    rw [e1]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    calc ‖H (h - g)‖ ≤ ‖H‖ * ‖h - g‖ := ContinuousLinearMap.le_opNorm H (h - g)
      _ ≤ 1 * ‖h - g‖ :=
          mul_le_mul_of_nonneg_right (UnforcedLeray.B0224.norm_heatH_le hc _) (norm_nonneg _)
      _ = ‖h - g‖ := one_mul _
  have hlim : Tendsto (fun s : ℝ =>
      ‖UnforcedLeray.B0224.dilH (Real.exp_pos (-s)) g - g‖ +
        ‖UnforcedLeray.B0224.heatH hc (UnforcedLeray.B0224.measurable_heatTime ν s) g - g‖)
      (𝓝[≥] 0) (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 (hD c g)).add
      (tendsto_iff_norm_sub_tendsto_zero.1 (hH c ν hc g))
    rwa [add_zero] at this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun s => norm_nonneg _) key hlim

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
