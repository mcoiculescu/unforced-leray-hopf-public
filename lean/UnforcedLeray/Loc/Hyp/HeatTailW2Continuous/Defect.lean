import UnforcedLeray.Loc.L09CompactDatum.Defect
import UnforcedLeray.Loc.L09CompactDatum.Background
import UnforcedLeray.Blueprint.Localization.Nonlinear

/-!
# H-HeatTail helper: the smoothed defect of an arbitrary compact datum

Helper of `Loc/Hyp/HeatTailW2Continuous.lean` (hypothesis `HeatTailW2Continuous` of
`Loc/L10Nonlinear.lean`; `paper/main.tex` lines 446–461, blueprint units B0718, B0720, B0722).

`HeatTailW2Continuous` quantifies over every datum `u₀` with `IsCompactDatum D u₀`, not only the
explicit `curl(χA_loc)` of step L9. From the clauses of `IsCompactDatum` (compact support,
smoothness off zero, `u₀ = u_dss` near zero) and of `IsExactBackground` (smoothness off zero,
the DSS law, `|D^k u_dss(x)| ≤ C_k|x|^{-1-k}` for `k ≤ 4`, lines 154–156), the defect
`d_loc = u₀ - u_dss` (line 446) agrees off zero with a globally smooth field `d̃`
(`L09.smoothDefect`) such that
* every derivative of `d̃` is bounded;
* `‖D^k d̃(x)‖ ‖x‖ ≤ C_k` far out for `k ≤ 4` (there `d̃ = -u_dss`);
* `K_loc(τ)(y) = e^{τ/2} [e^{he^τΔ} d̃](e^{τ/2} y)`: the value of `d_loc` at `0` is never seen.

Main declaration: `exists_smooth_defect`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Hyp.HeatTail

open UnforcedLeray.Blueprint UnforcedLeray.L09

variable {D : BackgroundData} {u₀ : SpatialField}

/-- Outside a ball the defect is `-u_dss`: the compact datum vanishes there. -/
theorem defect_far (hu : IsCompactDatum D u₀) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x : Space, R < ‖x‖ → (u₀ - D.udss) =ᶠ[𝓝 x] fun y => -D.udss y := by
  obtain ⟨R₀, hR₀⟩ := hu.datum.compact.isCompact.isBounded.subset_closedBall (0 : Space)
  refine ⟨max R₀ 1, le_max_right _ _, fun x hx => ?_⟩
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
  have hy' : y ∉ tsupport u₀ := fun hmem => by
    have h1 := hR₀ hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : max R₀ 1 < ‖y‖ := hy
    linarith [le_max_left R₀ 1]
  rw [Pi.sub_apply, image_eq_zero_of_notMem_tsupport hy', zero_sub]

/-- Every derivative of the defect is bounded on `‖x‖ ≥ ρ`, for every `ρ > 0`. -/
theorem defect_iteratedFDeriv_bounded (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀)
    {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    ∃ M : ℝ, ∀ x : Space, ρ ≤ ‖x‖ → ‖iteratedFDeriv ℝ n (u₀ - D.udss) x‖ ≤ M := by
  have hB := hD.background
  have hdss := dssField_of_exact hB
  obtain ⟨R, hR1, hfar⟩ := defect_far hu
  obtain ⟨M₁, hM₁⟩ := hdss.iteratedFDeriv_bounded_far n
  have hds : ContDiffOn ℝ ∞ (u₀ - D.udss) {0}ᶜ := hu.smooth_away.sub hB.udss_smooth
  set K : Set Space := {y | ρ ≤ ‖y‖ ∧ ‖y‖ ≤ R} with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall (0 : Space) R).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro y hy; simpa [Metric.mem_closedBall, dist_zero_right] using hy.2
  have hK0 : K ⊆ {0}ᶜ := by
    intro y hy h0
    rw [mem_singleton_iff] at h0
    have := hy.1
    rw [h0, norm_zero] at this
    linarith
  have hcont : ContinuousOn (iteratedFDeriv ℝ n (u₀ - D.udss)) {0}ᶜ :=
    ContinuousOn.continuousOn_iteratedFDeriv hds isOpen_compl_singleton
      (by exact_mod_cast le_top)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hK0)
  refine ⟨max M M₁, fun x hx => ?_⟩
  by_cases hxR : ‖x‖ ≤ R
  · exact (hM x ⟨hx, hxR⟩).trans (le_max_left _ _)
  · rw [not_le] at hxR
    rw [((hfar x hxR).iteratedFDeriv ℝ n).eq_of_nhds]
    change ‖iteratedFDeriv ℝ n (-D.udss) x‖ ≤ max M M₁
    rw [iteratedFDeriv_neg_apply, norm_neg]
    exact (hM₁ x (by linarith)).trans (le_max_right _ _)

/-- `‖D^n d_loc(x)‖ ‖x‖ ≤ C` far out, `n ≤ 4` (line 155: `|D^α u_dss| ≤ C|x|^{-1-|α|}`). -/
theorem defect_decay (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀) {n : ℕ}
    (hn : n ≤ 4) :
    ∃ C R : ℝ, 0 < R ∧ ∀ x : Space, R ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ n (u₀ - D.udss) x‖ * ‖x‖ ≤ C := by
  obtain ⟨R, hR1, hfar⟩ := defect_far hu
  obtain ⟨C, hC⟩ := hD.background.udss_bounds n hn
  refine ⟨C, R + 1, by linarith, fun x hx => ?_⟩
  have hxR : R < ‖x‖ := by linarith
  have hx1 : 1 ≤ ‖x‖ := by linarith
  have hx0 : x ≠ 0 := by
    intro h; rw [h, norm_zero] at hx1; linarith
  rw [((hfar x hxR).iteratedFDeriv ℝ n).eq_of_nhds]
  change ‖iteratedFDeriv ℝ n (-D.udss) x‖ * ‖x‖ ≤ C
  rw [iteratedFDeriv_neg_apply, norm_neg]
  calc ‖iteratedFDeriv ℝ n D.udss x‖ * ‖x‖
      ≤ ‖iteratedFDeriv ℝ n D.udss x‖ * ‖x‖ ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (le_self_pow₀ hx1 (Nat.succ_ne_zero n)) (norm_nonneg _)
    _ ≤ C := hC x hx0

/-- **The smoothed defect.** For an unstable background `D` and a compact datum `u₀`, there is
a globally smooth field `g` (the defect `d_loc = u₀ - u_dss` with its junk value at `0`
replaced) with all derivatives bounded, `‖D^n g(x)‖‖x‖ ≤ C` far out for `n ≤ 4`, and
`K_loc(τ)(y) = e^{τ/2} [e^{he^τΔ} g](e^{τ/2} y)` for every `τ` (line 446). -/
theorem exists_smooth_defect (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀) :
    ∃ g : SpatialField, ContDiff ℝ ∞ g ∧
      (∀ n : ℕ, ∃ M : ℝ, ∀ x : Space, ‖iteratedFDeriv ℝ n g x‖ ≤ M) ∧
      (∀ n : ℕ, n ≤ 4 → ∃ C R : ℝ, ∀ x : Space, R ≤ ‖x‖ →
        ‖iteratedFDeriv ℝ n g x‖ * ‖x‖ ≤ C) ∧
      ∀ τ : ℝ, heatTail D u₀ τ = fun y =>
        Real.exp (τ / 2) • Heat.average (D.h * Real.exp τ) g (Real.exp (τ / 2) • y) := by
  obtain ⟨r, hr, hnear⟩ := hu.agrees_near_zero
  have hd0 : ∀ x : Space, x ≠ 0 → ‖x‖ < r → (u₀ - D.udss) x = 0 := by
    intro x hx hxr
    rw [Pi.sub_apply, hnear x hx hxr, sub_self]
  have hds : ContDiffOn ℝ ∞ (u₀ - D.udss) {0}ᶜ :=
    hu.smooth_away.sub hD.background.udss_smooth
  refine ⟨smoothDefect r (u₀ - D.udss), smoothDefect_contDiff hr hd0 hds,
    smoothDefect_bounds hr hd0 (defect_iteratedFDeriv_bounded hD hu hr), fun n hn => ?_,
    fun τ => heatProfile_smoothDefect hd0 D.h τ⟩
  obtain ⟨C, R, hR, hCR⟩ := defect_decay hD hu hn
  refine ⟨C, R, fun x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    intro h; rw [h, norm_zero] at hx; linarith
  rw [((smoothDefect_eventuallyEq hd0 hx0).iteratedFDeriv ℝ n).eq_of_nhds]
  exact hCR x hx

end UnforcedLeray.Hyp.HeatTail
