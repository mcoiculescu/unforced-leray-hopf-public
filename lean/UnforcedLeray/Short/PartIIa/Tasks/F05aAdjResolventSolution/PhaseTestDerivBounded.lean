import UnforcedLeray.Short.PartIIa.Sub.F05_1

/-!
# Part II-a, task `PartII-a:F05a`: derivatives of a phase test are bounded

Target: `PhaseTestDerivBounded` (defined in `Short/PartII-a/Sub/F05_1.lean`, line 117).

Source of record: `the November 2 reference manuscript`, lines 1445-1451
(the smooth compact spatial test used in the adjoint resolvent passage).

Proof. `D^k Φ₀` is continuous. It is `P`-periodic in `τ`, because the translate
`Φ₀(· + (P, 0))` equals `Φ₀`. It vanishes on the open set `‖y‖ > R`, where `Φ₀` vanishes.
Reducing `τ` to `[0, P)` by periodicity (this uses `P > 0`), the values of `D^k Φ₀` lie in
the compact set `[0, P] × closedBall 0 R`, where they are bounded.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace

namespace UnforcedLeray.Short.PartIIa

namespace PhaseTestDerivBoundedAux

/-- A `P`-periodic phase test has `P`-periodic `k`-th derivative in `τ` on each fixed-`y` slice. -/
theorem iteratedFDeriv_slice_periodic {P : ℝ} {Φ₀ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ₀) (k : ℕ) (y : Space) :
    Function.Periodic (fun τ : ℝ => iteratedFDeriv ℝ k Φ₀ (τ, y)) P := by
  intro τ
  have hfun : (fun z : ℝ × Space => Φ₀ (z + ((P, 0) : ℝ × Space))) = Φ₀ := by
    funext z
    obtain ⟨s, w⟩ := z
    show Φ₀ ((s, w) + ((P, 0) : ℝ × Space)) = Φ₀ (s, w)
    have e : ((s, w) + ((P, 0) : ℝ × Space)) = (s + P, w) :=
      Prod.ext (by simp) (by simp)
    rw [e]
    exact hΦ.periodic s w
  have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := Φ₀) k ((P, 0) : ℝ × Space) (τ, y)
  rw [hfun] at h
  have e' : ((τ, y) + ((P, 0) : ℝ × Space)) = (τ + P, y) :=
    Prod.ext (by simp) (by simp)
  rw [e'] at h
  exact h.symm

/-- `D^k Φ₀` vanishes at `(τ, y)` when `‖y‖ > R`, since `Φ₀` vanishes on that open set. -/
theorem iteratedFDeriv_eq_zero_of_outside {R : ℝ} {Φ₀ : ℝ × Space → CVec3}
    (hR : ∀ τ y, R < ‖y‖ → Φ₀ (τ, y) = 0) (k : ℕ) (τ : ℝ) (y : Space) (hy : R < ‖y‖) :
    iteratedFDeriv ℝ k Φ₀ (τ, y) = 0 := by
  have hopen : IsOpen {q : ℝ × Space | R < ‖q.2‖} :=
    isOpen_lt continuous_const continuous_snd.norm
  have hmem : (τ, y) ∈ {q : ℝ × Space | R < ‖q.2‖} := hy
  have hev : Φ₀ =ᶠ[𝓝 (τ, y)] (fun _ : ℝ × Space => (0 : CVec3)) := by
    filter_upwards [hopen.mem_nhds hmem] with q hq
    exact hR q.1 q.2 hq
  have h2 := hev.iteratedFDeriv ℝ k
  have h3 : iteratedFDeriv ℝ k Φ₀ (τ, y)
      = iteratedFDeriv ℝ k (fun _ : ℝ × Space => (0 : CVec3)) (τ, y) :=
    h2.eq_of_nhds
  rw [h3]
  simp [iteratedFDeriv_fun_zero]

end PhaseTestDerivBoundedAux

/-- **Derivatives of a phase test are bounded** (`P > 0`): `D^kΦ₀` is bounded on `ℝ × Space`. -/
theorem phaseTestDerivBounded_proof : UnforcedLeray.Short.PartIIa.PhaseTestDerivBounded := by
  intro P hP Φ₀ hΦ k
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hcont : Continuous (iteratedFDeriv ℝ k Φ₀) :=
    hΦ.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hK : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun p => ?_⟩
  obtain ⟨τ, y⟩ := p
  by_cases hy : R < ‖y‖
  · rw [PhaseTestDerivBoundedAux.iteratedFDeriv_eq_zero_of_outside hR k τ y hy, norm_zero]
    exact le_max_right _ _
  · have hy' : ‖y‖ ≤ R := not_lt.mp hy
    obtain ⟨τ', hτ', heq⟩ :=
      (PhaseTestDerivBoundedAux.iteratedFDeriv_slice_periodic hΦ k y).exists_mem_Ico₀ hP τ
    have hmem : (τ', y) ∈ Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R :=
      ⟨⟨hτ'.1, hτ'.2.le⟩, by simpa using hy'⟩
    have h1 := hC (τ', y) hmem
    have heq' : iteratedFDeriv ℝ k Φ₀ (τ, y) = iteratedFDeriv ℝ k Φ₀ (τ', y) := heq
    rw [heq']
    exact le_trans h1 (le_max_left _ _)

end UnforcedLeray.Short.PartIIa
