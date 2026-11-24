import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Riemann sums of a continuous function

Helper facts for the three analytic statements `l2SqMeas`, `l2SqDiff`, `l2SqWeak`.
The uniform left-endpoint Riemann sums of a continuous `h` converge to `∫ₐᵇ h`, pointwise in
the parameters; no measurability in the integration variable is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace UnforcedLeray.Short.PartI.L2SqDeriv

theorem riemann_point_mem (a b : ℝ) {n k : ℕ} (hk : k ≤ n) (hn : 0 < n) :
    a + (k : ℝ) * ((b - a) / n) ∈ uIcc a b := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  have h0 : 0 ≤ (k : ℝ) / n := by positivity
  have h1 : (k : ℝ) / n ≤ 1 := (div_le_one hn').2 hk'
  have hx : a + (k : ℝ) * ((b - a) / n) = a + ((k : ℝ) / n) * (b - a) := by ring
  rw [hx]
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab]
    constructor
    · nlinarith [mul_nonneg h0 (sub_nonneg.2 hab)]
    · nlinarith [mul_le_mul_of_nonneg_right h1 (sub_nonneg.2 hab)]
  · rw [uIcc_of_ge hab]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right h1 (sub_nonneg.2 hab)]
    · nlinarith [mul_nonneg h0 (sub_nonneg.2 hab)]

theorem abs_sub_le_of_mem_uIcc' {x u v : ℝ} (hx : x ∈ uIcc u v) : |x - u| ≤ |v - u| := by
  rcases le_total u v with huv | huv
  · rw [uIcc_of_le huv] at hx
    rw [abs_of_nonneg (show (0 : ℝ) ≤ x - u by linarith [hx.1]),
      abs_of_nonneg (show (0 : ℝ) ≤ v - u by linarith)]
    linarith [hx.2]
  · rw [uIcc_of_ge huv] at hx
    rw [abs_of_nonpos (show x - u ≤ 0 by linarith [hx.2]),
      abs_of_nonpos (show v - u ≤ 0 by linarith)]
    linarith [hx.1]

/-- Left-endpoint Riemann sums of a continuous function converge to the interval integral. -/
theorem tendsto_riemannSum (h : ℝ → ℝ) (hh : Continuous h) (a b : ℝ) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (b - a) / n * h (a + (k : ℝ) * ((b - a) / n)))
      atTop (𝓝 (∫ t in a..b, h t)) := by
  have hunif : UniformContinuousOn h (uIcc a b) :=
    IsCompact.uniformContinuousOn_of_continuous isCompact_uIcc hh.continuousOn
  have key : ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n →
      dist (∑ k ∈ Finset.range n, (b - a) / n * h (a + (k : ℝ) * ((b - a) / n)))
        (∫ t in a..b, h t) ≤ ε * |b - a| := by
    intro ε hε
    obtain ⟨η, hη, hηc⟩ := Metric.uniformContinuousOn_iff.1 hunif ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (|b - a| / η)
    refine ⟨N + 1, fun n hn => ?_⟩
    have hn0 : 0 < n := by omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hn'' : (n : ℝ) ≠ 0 := ne_of_gt hn'
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (b - a) / n := ⟨_, rfl⟩
    rw [← hδ]
    have hδη : |δ| < η := by
      rw [hδ, abs_div, abs_of_pos hn', div_lt_iff₀ hn']
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast (by omega : N ≤ n)
      have h2 : |b - a| / η < n := lt_of_lt_of_le hN hNn
      rw [div_lt_iff₀ hη] at h2
      linarith
    have hpk : ∀ k, k ≤ n → a + (k : ℝ) * δ ∈ uIcc a b := fun k hk => by
      rw [hδ]; exact riemann_point_mem a b hk hn0
    have hpn : a + (n : ℝ) * δ = b := by
      have : (n : ℝ) * δ = b - a := by rw [hδ]; field_simp
      linarith
    have hp0 : a + ((0 : ℕ) : ℝ) * δ = a := by simp
    have hint : ∀ k < n, IntervalIntegrable h volume (a + (k : ℝ) * δ)
        (a + ((k + 1 : ℕ) : ℝ) * δ) :=
      fun k _ => hh.intervalIntegrable _ _
    have htel := intervalIntegral.sum_integral_adjacent_intervals
      (f := h) (μ := volume) (a := fun k : ℕ => a + (k : ℝ) * δ) hint
    rw [hp0, hpn] at htel
    have hconst : ∀ k ∈ Finset.range n,
        δ * h (a + (k : ℝ) * δ)
          = ∫ t in a + (k : ℝ) * δ..a + ((k + 1 : ℕ) : ℝ) * δ, h (a + (k : ℝ) * δ) := by
      intro k _
      rw [intervalIntegral.integral_const, smul_eq_mul]
      push_cast
      ring
    have hsplit : ∀ k : ℕ,
        ∫ t in a + (k : ℝ) * δ..a + ((k + 1 : ℕ) : ℝ) * δ, (h t - h (a + (k : ℝ) * δ))
          = (∫ t in a + (k : ℝ) * δ..a + ((k + 1 : ℕ) : ℝ) * δ, h t)
            - ∫ t in a + (k : ℝ) * δ..a + ((k + 1 : ℕ) : ℝ) * δ, h (a + (k : ℝ) * δ) :=
      fun k => intervalIntegral.integral_sub (hh.intervalIntegrable _ _) intervalIntegrable_const
    have hdiff : ∑ k ∈ Finset.range n,
        ∫ t in a + (k : ℝ) * δ..a + ((k + 1 : ℕ) : ℝ) * δ, (h t - h (a + (k : ℝ) * δ))
          = (∫ t in a..b, h t) - ∑ k ∈ Finset.range n, δ * h (a + (k : ℝ) * δ) := by
      simp only [hsplit]
      rw [Finset.sum_sub_distrib, htel, Finset.sum_congr rfl hconst]
    have hbound : ∀ k ∈ Finset.range n,
        ‖∫ t in a + (k : ℝ) * δ..a + ((k + 1 : ℕ) : ℝ) * δ, (h t - h (a + (k : ℝ) * δ))‖
          ≤ ε * |δ| := by
      intro k hk
      have hk' : k < n := Finset.mem_range.1 hk
      have hpd : a + ((k + 1 : ℕ) : ℝ) * δ - (a + (k : ℝ) * δ) = δ := by push_cast; ring
      have hside : ∀ x ∈ uIoc (a + (k : ℝ) * δ) (a + ((k + 1 : ℕ) : ℝ) * δ),
          ‖(fun t => h t - h (a + (k : ℝ) * δ)) x‖ ≤ ε := by
        intro x hx
        have hxI' : x ∈ uIcc (a + (k : ℝ) * δ) (a + ((k + 1 : ℕ) : ℝ) * δ) :=
          uIoc_subset_uIcc hx
        have hxI : x ∈ uIcc a b :=
          uIcc_subset_uIcc (hpk k (by omega)) (hpk (k + 1) (by omega)) hxI'
        have hxd := abs_sub_le_of_mem_uIcc' hxI'
        rw [hpd] at hxd
        have hdist : dist x (a + (k : ℝ) * δ) < η := by
          rw [Real.dist_eq]; exact lt_of_le_of_lt hxd hδη
        have hc := hηc x hxI _ (hpk k (by omega)) hdist
        rw [Real.dist_eq] at hc
        simp only [Real.norm_eq_abs]
        exact hc.le
      have hC := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun t => h t - h (a + (k : ℝ) * δ)) (C := ε) hside
      rw [hpd] at hC
      exact hC
    have hS : ‖∑ k ∈ Finset.range n,
        ∫ t in a + (k : ℝ) * δ..a + ((k + 1 : ℕ) : ℝ) * δ, (h t - h (a + (k : ℝ) * δ))‖
          ≤ ∑ k ∈ Finset.range n, ε * |δ| :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hbound)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hS
    have hn_abs : (n : ℝ) * |δ| = |b - a| := by
      rw [hδ, abs_div, abs_of_pos hn']
      field_simp
    have hfin : (n : ℝ) * (ε * |δ|) = ε * |b - a| := by rw [← hn_abs]; ring
    have hRI : ∑ k ∈ Finset.range n, δ * h (a + (k : ℝ) * δ) - (∫ t in a..b, h t)
        = -(∑ k ∈ Finset.range n,
          ∫ t in a + (k : ℝ) * δ..a + ((k + 1 : ℕ) : ℝ) * δ, (h t - h (a + (k : ℝ) * δ))) := by
      rw [hdiff]; ring
    rw [dist_eq_norm, hRI, norm_neg]
    linarith [hS, hfin]
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := key (ε / (|b - a| + 1)) (by positivity)
  refine ⟨N, fun n hn => lt_of_le_of_lt (hN n hn) ?_⟩
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith [abs_nonneg (b - a)]

end UnforcedLeray.Short.PartI.L2SqDeriv
