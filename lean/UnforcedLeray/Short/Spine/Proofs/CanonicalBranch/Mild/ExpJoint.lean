import UnforcedLeray.Cons.L2.CanonicalBranch.Evolution

/-!
# Helper for `Spine:SP-CAN` Bridge 3: joint continuity of `e^{aD} x`

Helper module of `Short/Spine/Proofs/CanonicalBranch/Mild.lean` (task `Spine:SP-CAN`, Bridge 3
`StrongCanonicalIsMild`, source `the November 2 reference manuscript` lines
1094-1150). The map `(a, x) ↦ e^{aD} x` is jointly continuous, because `‖e^{aD}‖ ≤ 1` and
`a ↦ e^{aD} y` is continuous for each fixed `y` (`Cons.G3b.continuous_expD_apply`).

Main declarations (namespace `UnforcedLeray.Short.Spine.CanonicalMild`):
* `continuous_expD_joint`: `Continuous fun p : ℝ × XG => expD p.1 p.2`;
* `continuousOn_expD_pair`: `v ↦ e^{f(v)D} y(v)` is continuous on `s` when `f` and `y` are;
* `continuousOn_log_sub`: `v ↦ log v - log θ` is continuous on a set of positive reals;
* `intervalIntegrable_expD_log`: `v ↦ e^{(log v - log θ)D} y(v)` is interval integrable on `θ..θ'`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.Spine.CanonicalMild

open UnforcedLeray.B0010 UnforcedLeray.B0123

/-- Joint continuity of `(a, x) ↦ e^{aD} x`. -/
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

/-- Composition with the joint continuous map: `v ↦ e^{f(v)D} y(v)` is continuous on `s` when
`f` and `y` are. (The composition is unfolded by `congr` to avoid an elaboration timeout.) -/
theorem continuousOn_expD_pair {α : Type*} [TopologicalSpace α] {s : Set α} {f : α → ℝ}
    {y : α → XG} (hf : ContinuousOn f s) (hy : ContinuousOn y s) :
    ContinuousOn (fun v => expD (f v) (y v)) s := by
  have hp : ContinuousOn (fun v => (f v, y v)) s := hf.prodMk hy
  refine ContinuousOn.congr (f := fun v => (fun q : ℝ × XG => expD q.1 q.2) (f v, y v)) ?_ ?_
  · exact continuous_expD_joint.continuousOn.comp hp (mapsTo_univ _ _)
  · intro v _
    rfl

/-- `v ↦ log v - log θ` is continuous on a set where `v > 0`. -/
theorem continuousOn_log_sub {θ : ℝ} {s : Set ℝ} (hs : ∀ v ∈ s, 0 < v) :
    ContinuousOn (fun v : ℝ => Real.log v - Real.log θ) s := by
  have hlog : ContinuousOn (fun v : ℝ => Real.log v) s := by
    apply ContinuousOn.log continuousOn_id
    intro v hv
    exact (hs v hv).ne'
  exact ContinuousOn.sub hlog continuousOn_const

/-- The integrand `v ↦ e^{(log v - log θ)D} y(v)` is interval integrable on `θ..θ'`. -/
theorem intervalIntegrable_expD_log {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') {y : ℝ → XG}
    (hy : ContinuousOn y (Icc θ θ')) :
    IntervalIntegrable (fun v : ℝ => expD (Real.log v - Real.log θ) (y v)) volume θ θ' := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hθθ']
  exact continuousOn_expD_pair (continuousOn_log_sub (fun v hv => lt_of_lt_of_le hθ hv.1)) hy

end UnforcedLeray.Short.Spine.CanonicalMild
