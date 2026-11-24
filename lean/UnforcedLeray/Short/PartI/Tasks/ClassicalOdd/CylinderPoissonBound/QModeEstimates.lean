import UnforcedLeray.Short.PartI.Sub.T02_3_8

/-!
# Part I, task `PartI:T02/3/8/QModeEstimates`: the `q`-mode estimates

Target: `CylPoisQModeEstimates` (`Short/PartI/Sub/T02_3_8.lean`, Leaf O3).
Source of record: `the November 2 reference manuscript`, lines 276-288.

Proof.  By `Cyl.qMode_eq_integral` the `n`-th mode at height `η` is
`(1/c) ∫_{-c/2}^{c/2} fourier(-n)(q) f(q, η) dq`, and `fourier(-n)` has modulus one.  If
`|f(q, η)| ≤ K` for all `q`, the integral has norm at most `K c`, so the mode has norm at most `K`
(slice bound `cpQE_slice_bound`, which uses only the slice at height `η`).  If `f → 0` along
`|z.2| → ∞`, then for each `δ > 0` there is `R` with `|f(q, η)| < δ` for all `q` whenever `|η| ≥ R`
(`cpQE_tail`); the slice bound then gives `|qMode| ≤ δ` for `|η| ≥ R`, which is the
`cocompact ℝ` limit (`cocompact_eq_atBot_atTop`).
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The `fourier` monomials have modulus one at every point. -/
theorem cpQE_norm_fourier {T : ℝ} (m : ℤ) (x : AddCircle T) : ‖fourier m x‖ = 1 :=
  Circle.norm_coe _

/-- Slice bound: if `‖f (q, η)‖ ≤ K` for all `q`, then the `n`-th `q`-mode at height `η` has norm
at most `K`. -/
theorem cpQE_slice_bound {c : ℝ} (hc : 0 < c) (n : ℤ) (f : Plane → ℂ) (η K : ℝ)
    (hK : ∀ q : ℝ, ‖f (q, η)‖ ≤ K) : ‖Cyl.qMode c hc n f η‖ ≤ K := by
  have hint : ‖∫ q in (-c / 2)..(c / 2),
      fourier (-n) (q : AddCircle (c / 2 - -c / 2)) • f (q, η)‖ ≤ K * |c / 2 - -c / 2| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x _
    rw [norm_smul, cpQE_norm_fourier, one_mul]
    exact hK x
  have habs : |c / 2 - -c / 2| = c := by
    rw [Cyl.half_sub_neg_half, abs_of_pos hc]
  rw [habs] at hint
  have hs : ‖(1 / (c / 2 - -c / 2) : ℝ)‖ = 1 / c := by
    rw [Real.norm_eq_abs, Cyl.half_sub_neg_half, abs_of_pos (one_div_pos.2 hc)]
  rw [Cyl.qMode_eq_integral, norm_smul, hs, one_div, inv_mul_le_iff₀ hc]
  exact hint.trans (le_of_eq (mul_comm K c))

/-- Tail of the decay hypothesis: if `f → 0` along `|z.2| → ∞`, then for each `δ > 0` there is
`R` such that `‖f (q, η)‖ < δ` for every `q` whenever `R ≤ |η|`. -/
theorem cpQE_tail {f : Plane → ℂ}
    (hf : Tendsto f (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, ∀ q η : ℝ, R ≤ |η| → ‖f (q, η)‖ < δ := by
  have h1 : ∀ᶠ z in comap (fun z : Plane => |z.2|) atTop, f z ∈ Metric.ball (0 : ℂ) δ :=
    hf.eventually (Metric.ball_mem_nhds _ hδ)
  rw [Filter.eventually_comap] at h1
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 h1
  refine ⟨R, fun q η hη => ?_⟩
  have hmem := hR (|η|) hη (q, η) rfl
  rwa [Metric.mem_ball, dist_zero_right] at hmem

/-- **Leaf O3** (`CylPoisQModeEstimates`): the `q`-modes of a bounded `f` are bounded by the same
constant, and the modes of an `f` decaying as `|η| → ∞` decay at `cocompact ℝ`. -/
theorem cylPoisQModeEstimates : CylPoisQModeEstimates := by
  intro c hc n f
  refine ⟨fun K hK η => cpQE_slice_bound hc n f η K (fun q => hK (q, η)), fun hf => ?_⟩
  rw [cocompact_eq_atBot_atTop, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR⟩ := cpQE_tail hf (half_pos hε)
  refine Filter.eventually_sup.2 ⟨?_, ?_⟩
  · rw [Filter.eventually_atBot]
    refine ⟨-R, fun η hη => ?_⟩
    have hRη : R ≤ |η| := by
      rcases abs_cases η with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    rw [dist_zero_right]
    exact lt_of_le_of_lt (cpQE_slice_bound hc n f η (ε / 2) (fun q => (hR q η hRη).le))
      (half_lt_self hε)
  · rw [Filter.eventually_atTop]
    refine ⟨R, fun η hη => ?_⟩
    have hRη : R ≤ |η| := hη.trans (le_abs_self η)
    rw [dist_zero_right]
    exact lt_of_le_of_lt (cpQE_slice_bound hc n f η (ε / 2) (fun q => (hR q η hRη).le))
      (half_lt_self hε)

end UnforcedLeray.Short.PartI
