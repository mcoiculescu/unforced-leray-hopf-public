import UnforcedLeray.Short.Interface.Statements

/-!
# Interface:I06 (helper 2b-1): the periodization of a similarity test is a periodic test

Target `periodizeIsPeriodicTest : PeriodizeIsPeriodicTest` (`Statements.lean`, Section 2b; source
of record `the November 2 reference manuscript`, the periodic test of the mode
equation, lines 164-185). For `P > 0` and a similarity test `ψ` (smooth, compactly supported),
the periodization `periodizeTest P ψ (τ, y) = ∑ᶠ k, ψ(τ + kP, y)` is an `IsPeriodicTest P`:

* `periodic`: the index shift `k ↦ k + 1` is an equivalence of `ℤ` (`finsum_comp_equiv`).
* `space_compact`: `K := Prod.snd '' tsupport ψ` is compact, and a point `(τ, y)` with `y ∉ K`
  has every term `ψ(τ + kP, y)` equal to zero (`finsum_eq_zero_of_forall_eq_zero`).
* `smooth`: the time support of `ψ` is bounded, so on a window `|s - t₀| < 1` only the finitely
  many indices `|k| ≤ N` contribute. The periodization is therefore locally a finite sum of
  smooth translates `ψ(· + kP, ·)`, which is smooth (`ContDiff.sum`).

Unconditional: no hypothesis is added to the target. The window argument follows the proof of
`periodizeCommutes` (`Leaf2_Commutes.lean`), restated here so that this file imports only
`Statements.lean`.
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

/-- Time support of a similarity test: there is a radius `R` such that `ψ(u, y) = 0` whenever
`u` lies outside `[-R, R]`. -/
theorem leaf2pt_time_support (ψ : SpaceTime → Space) (hψ : IsSimilarityTest ψ) :
    ∃ R : ℝ, ∀ (u : ℝ) (y : Space), (R < u ∨ u < -R) → ψ (u, y) = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : SpaceTime)).mp
    hψ.compact.isCompact.isBounded
  refine ⟨R, fun u y hu => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have h1 : ‖((u, y) : SpaceTime)‖ ≤ R := by
    have h0 := hR hmem
    rwa [Metric.mem_closedBall, dist_zero_right] at h0
  have h2 : |u| ≤ ‖((u, y) : SpaceTime)‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_fst_le ((u, y) : SpaceTime)
  have h3 : R < |u| := by
    rcases hu with h | h
    · exact lt_of_lt_of_le h (le_abs_self u)
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
  linarith

/-- Local finiteness of the periodization: on a unit window `|s - t₀| < 1` only the indices
`-N ≤ k ≤ N` contribute, for one fixed `N`. -/
theorem leaf2pt_local_finite (P : ℝ) (hP : 0 < P) (ψ : SpaceTime → Space)
    (hψ : IsSimilarityTest ψ) (t₀ : ℝ) :
    ∃ N : ℤ, ∀ s : ℝ, |s - t₀| < 1 → ∀ y : Space,
      periodizeTest P ψ (s, y) = ∑ k ∈ Finset.Icc (-N) N, ψ (s + (k : ℝ) * P, y) := by
  obtain ⟨R, hR⟩ := leaf2pt_time_support ψ hψ
  have hP0 : P ≠ 0 := ne_of_gt hP
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (R + 1 + |t₀|) / P := ⟨_, rfl⟩
  have hcP : c * P = R + 1 + |t₀| := by
    rw [hc]
    field_simp
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = ⌈c⌉ := ⟨_, rfl⟩
  have hNc : c ≤ (N : ℝ) := by
    rw [hN]
    exact Int.le_ceil c
  refine ⟨N, fun s hs y => ?_⟩
  obtain ⟨hs1, hs2⟩ := abs_lt.mp hs
  have ht1 : t₀ ≤ |t₀| := le_abs_self t₀
  have ht2 : -|t₀| ≤ t₀ := neg_abs_le t₀
  unfold periodizeTest
  apply finsum_eq_sum_of_support_subset
  intro k hk
  rw [Function.mem_support] at hk
  rw [Finset.mem_coe, Finset.mem_Icc]
  by_contra hkN
  apply hk
  show ψ (s + (k : ℝ) * P, y) = 0
  apply hR
  have hkN' : k < -N ∨ N < k := by omega
  rcases hkN' with h | h
  · have h' : (k : ℝ) < -(N : ℝ) := by exact_mod_cast h
    have hk' : (k : ℝ) < -c := by linarith
    have hkP := mul_lt_mul_of_pos_right hk' hP
    rw [neg_mul, hcP] at hkP
    right
    linarith
  · have h' : (N : ℝ) < (k : ℝ) := by exact_mod_cast h
    have hk' : c < (k : ℝ) := by linarith
    have hkP := mul_lt_mul_of_pos_right hk' hP
    rw [hcP] at hkP
    left
    linarith

theorem periodizeIsPeriodicTest : PeriodizeIsPeriodicTest := by
  unfold PeriodizeIsPeriodicTest
  intro P ψ hP hψ
  refine ⟨?_, ?_, ?_⟩
  · -- Smoothness: locally a finite sum of smooth translates.
    rw [contDiff_iff_contDiffAt]
    intro z0
    obtain ⟨N, hN⟩ := leaf2pt_local_finite P hP ψ hψ z0.1
    have hterm : ∀ k : ℤ, ContDiff ℝ ∞ (fun z : SpaceTime => ψ (z.1 + (k : ℝ) * P, z.2)) := by
      intro k
      have hmap : ContDiff ℝ ∞ (fun z : SpaceTime => ((z.1 + (k : ℝ) * P, z.2) : SpaceTime)) :=
        (contDiff_fst.add contDiff_const).prodMk contDiff_snd
      exact hψ.smooth.comp hmap
    have hsum : ContDiff ℝ ∞
        (fun z : SpaceTime => ∑ k ∈ Finset.Icc (-N) N, ψ (z.1 + (k : ℝ) * P, z.2)) :=
      ContDiff.sum (f := fun (k : ℤ) (z : SpaceTime) => ψ (z.1 + (k : ℝ) * P, z.2))
        (fun k _ => hterm k)
    have hball : ∀ᶠ z : SpaceTime in 𝓝 z0, z.1 ∈ Metric.ball z0.1 1 :=
      (continuous_fst.tendsto z0).eventually (Metric.ball_mem_nhds z0.1 zero_lt_one)
    have hev : (periodizeTest P ψ) =ᶠ[𝓝 z0]
        (fun z : SpaceTime => ∑ k ∈ Finset.Icc (-N) N, ψ (z.1 + (k : ℝ) * P, z.2)) := by
      filter_upwards [hball] with z hz
      rw [Metric.mem_ball, Real.dist_eq] at hz
      exact hN z.1 hz z.2
    exact hsum.contDiffAt.congr_of_eventuallyEq hev
  · -- Periodicity in the phase: the shift `k ↦ k + 1` reindexes the sum.
    intro z
    show (∑ᶠ k : ℤ, ψ (z.1 + P + (k : ℝ) * P, z.2)) = ∑ᶠ k : ℤ, ψ (z.1 + (k : ℝ) * P, z.2)
    have hg : ∀ k : ℤ, ψ (z.1 + P + (k : ℝ) * P, z.2) =
        ψ (z.1 + ((k + 1 : ℤ) : ℝ) * P, z.2) := by
      intro k
      have h : z.1 + P + (k : ℝ) * P = z.1 + ((k + 1 : ℤ) : ℝ) * P := by
        push_cast
        ring
      rw [h]
    calc (∑ᶠ k : ℤ, ψ (z.1 + P + (k : ℝ) * P, z.2))
        = ∑ᶠ k : ℤ, ψ (z.1 + ((k + 1 : ℤ) : ℝ) * P, z.2) := finsum_congr hg
      _ = ∑ᶠ k : ℤ, ψ (z.1 + (k : ℝ) * P, z.2) :=
          finsum_comp_equiv (Equiv.addRight (1 : ℤ))
            (f := fun k : ℤ => ψ (z.1 + (k : ℝ) * P, z.2))
  · -- Compact support in space: the image of the compact time-space support under `snd`.
    refine ⟨Prod.snd '' tsupport ψ, hψ.compact.isCompact.image continuous_snd, ?_⟩
    intro z hz
    show (∑ᶠ k : ℤ, ψ (z.1 + (k : ℝ) * P, z.2)) = 0
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hz ⟨(z.1 + (k : ℝ) * P, z.2), hmem, rfl⟩

end UnforcedLeray.Short.Interface
