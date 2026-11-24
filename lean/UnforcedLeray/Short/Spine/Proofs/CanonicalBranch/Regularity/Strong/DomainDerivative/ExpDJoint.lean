import UnforcedLeray.Short.Spine.Sub.SP_CAN4_2_1

/-!
# Spine: joint continuity of `(a, x) ↦ e^{aD} x` (task `Spine:SP-CAN/4/2/1/3`)

Source: `the November 2 reference manuscript` line 1086 and lines 1134-1145.

`‖e^{aD}‖ ≤ 1` for every `a` (`B0123.norm_expD_le`), and `a ↦ e^{aD} y` is continuous for each
fixed `y` (`Cons.G3b.continuous_expD_apply`). Together these give joint continuity by the
estimate `‖e^{aD}x - e^{a₀D}x₀‖ ≤ ‖x - x₀‖ + ‖e^{aD}x₀ - e^{a₀D}x₀‖`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 UnforcedLeray.B0123

/-- Joint continuity of `(a, x) ↦ e^{aD} x` on `ℝ × XG`. -/
theorem continuous_expD_joint : Continuous fun p : ℝ × XG => expD p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨b, y⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun p : ℝ × XG => ‖p.2 - y‖) (𝓝 (b, y)) (𝓝 0) := by
    have hc : Continuous fun p : ℝ × XG => ‖p.2 - y‖ := by fun_prop
    simpa using hc.tendsto (b, y)
  have h2 : Tendsto (fun p : ℝ × XG => ‖expD p.1 y - expD b y‖) (𝓝 (b, y)) (𝓝 0) := by
    have hc : Continuous fun p : ℝ × XG => expD p.1 y :=
      (UnforcedLeray.Cons.G3b.continuous_expD_apply y).comp continuous_fst
    exact tendsto_iff_norm_sub_tendsto_zero.1 (hc.tendsto (b, y))
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine squeeze_zero (fun p => norm_nonneg _) (fun p => ?_) h3
  show ‖expD p.1 p.2 - expD b y‖ ≤ ‖p.2 - y‖ + ‖expD p.1 y - expD b y‖
  have hsplit : expD p.1 p.2 - expD b y = expD p.1 (p.2 - y) + (expD p.1 y - expD b y) := by
    rw [map_sub]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact ((expD p.1).le_opNorm (p.2 - y)).trans (mul_le_of_le_one_left (norm_nonneg _) (norm_expD_le p.1))

end UnforcedLeray.Short.Spine
