import UnforcedLeray.Lib.PhaseSpace.Ops
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/1/4/2`: bound on `∂_{y_j} Φ` for a phase test

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 3256-3268, 4284-4286.

The target as originally stated is false at `P = 0` (take `Φ = τ² χ(y) e₀`), so the
hypothesis `0 < P` is added (every use has `P = 2c/R > 0`).  Names corrected to
`UnforcedLeray.PhaseSpace.CVec3` and `UnforcedLeray.Space`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric

theorem dy_phaseTest_bound : ∀ (P Y : ℝ), 0 < P →
    ∀ (Φ : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3),
    UnforcedLeray.PhaseSpace.IsPhaseTest P Φ → (∀ τ y, Y < ‖y‖ → Φ (τ, y) = 0) →
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ (x : ℝ × UnforcedLeray.Space) (j : Fin 3) (i : Fin 3),
        ‖UnforcedLeray.PhaseSpace.dy j Φ x i‖ ≤ B) ∧
      (∀ (x : ℝ × UnforcedLeray.Space) (j : Fin 3), Y < ‖x.2‖ →
        UnforcedLeray.PhaseSpace.dy j Φ x = 0) := by
  intro P Y hP Φ hΦ hsupp
  have hzero : ∀ (x : ℝ × UnforcedLeray.Space) (j : Fin 3), Y < ‖x.2‖ →
      UnforcedLeray.PhaseSpace.dy j Φ x = 0 := by
    intro x j hx
    have hopen : IsOpen {p : ℝ × UnforcedLeray.Space | Y < ‖p.2‖} :=
      isOpen_lt continuous_const (continuous_snd.norm)
    have hev : Φ =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hopen.mem_nhds hx] with p hp
      exact hsupp p.1 p.2 hp
    have : fderiv ℝ Φ x = fderiv ℝ (fun _ : ℝ × UnforcedLeray.Space => (0 : UnforcedLeray.PhaseSpace.CVec3)) x := hev.fderiv_eq
    simp [UnforcedLeray.PhaseSpace.dy, this]
  let G : ℝ × UnforcedLeray.Space → ℝ :=
    fun p => ∑ j : Fin 3, ‖UnforcedLeray.PhaseSpace.dy j Φ p‖
  have hGc : Continuous G :=
    continuous_finsetSum _ fun j _ => (hΦ.dy j).smooth.continuous.norm
  have hGp : ∀ τ y, G (τ + P, y) = G (τ, y) := by
    intro τ y
    simp only [G]
    exact Finset.sum_congr rfl fun j _ => by rw [(hΦ.dy j).periodic τ y]
  have hK : IsCompact (Icc (0:ℝ) P ×ˢ closedBall (0 : UnforcedLeray.Space) Y) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hGc.continuousOn
  have hG : ∀ x : ℝ × UnforcedLeray.Space, G x ≤ |C| := by
    intro x
    by_cases hy : Y < ‖x.2‖
    · have : G x = 0 := by
        simp only [G]
        exact Finset.sum_eq_zero fun j _ => by rw [hzero x j hy]; simp
      rw [this]; exact abs_nonneg _
    · have hper : Function.Periodic (fun τ => G (τ, x.2)) P := fun τ => hGp τ x.2
      obtain ⟨t, ht, hx⟩ := hper.exists_mem_Ico₀ hP x.1
      have hmem : (t, x.2) ∈ Icc (0:ℝ) P ×ˢ closedBall (0 : UnforcedLeray.Space) Y :=
        ⟨⟨ht.1, ht.2.le⟩, by simpa using not_lt.mp hy⟩
      have h1 := hC _ hmem
      have : G x = G (t, x.2) := hx
      rw [this]
      calc G (t, x.2) ≤ ‖G (t, x.2)‖ := le_abs_self _
        _ ≤ C := h1
        _ ≤ |C| := le_abs_self _
  refine ⟨|C|, abs_nonneg _, fun x j i => ?_, hzero⟩
  calc ‖UnforcedLeray.PhaseSpace.dy j Φ x i‖
      ≤ ‖UnforcedLeray.PhaseSpace.dy j Φ x‖ := PiLp.norm_apply_le _ i
    _ ≤ G x := Finset.single_le_sum (f := fun j => ‖UnforcedLeray.PhaseSpace.dy j Φ x‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ |C| := hG x

end
