import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.Defs

/-!
# `PeriodicBump`

A smooth function supported in `(0,P)` extends to a smooth `P`-periodic function, namely the
periodisation `s t = ∑ₙ s₀(t - nP)`. Locally in `t` only finitely many terms are nonzero, so the
periodisation is smooth. Source `the November 2 reference manuscript` lines
1334-1337 and 1351-1362.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem periodicBump : PeriodicBump := by
  intro P hP s0 hs0 _hc hsupp
  refine ⟨fun t => ∑ᶠ n : ℤ, s0 (t - (n : ℝ) * P), ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt (|x| / P)
    have hNP : |x| < (N : ℝ) * P := (div_lt_iff₀ hP).1 hN
    have hx1 : -((N : ℝ) * P) < x := by
      have := neg_abs_le x
      linarith
    have hx2 : x < (N : ℝ) * P := lt_of_le_of_lt (le_abs_self x) hNP
    have hloc : ∀ t ∈ Ioo (-((N : ℝ) * P)) ((N : ℝ) * P),
        ∑ᶠ n : ℤ, s0 (t - (n : ℝ) * P) = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), s0 (t - (n : ℝ) * P) := by
      intro t ht
      obtain ⟨ht1, ht2⟩ := ht
      apply finsum_eq_sum_of_support_subset
      intro n hn
      rw [Function.mem_support] at hn
      have hmem : t - (n : ℝ) * P ∈ Ioo 0 P := by
        by_contra hc
        exact hn (image_eq_zero_of_notMem_tsupport (fun h => hc (hsupp h)))
      obtain ⟨h0, h1⟩ := hmem
      have k1 : (-(N : ℝ)) < (n : ℝ) + 1 := lt_of_mul_lt_mul_right (by linarith) hP.le
      have k2 : (n : ℝ) < (N : ℝ) := lt_of_mul_lt_mul_right (by linarith) hP.le
      have k1' : -(N : ℤ) - 1 < n := by
        exact_mod_cast (show ((-(N : ℤ) - 1 : ℤ) : ℝ) < (n : ℝ) by push_cast; linarith)
      have k2' : n < (N : ℤ) := by exact_mod_cast k2
      exact Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have hcd : ContDiffAt ℝ ∞
        (fun t => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), s0 (t - (n : ℝ) * P)) x := by
      apply ContDiff.contDiffAt
      apply ContDiff.sum
      intro n _
      exact hs0.comp (f := fun t : ℝ => t - (n : ℝ) * P) (by fun_prop)
    exact hcd.congr_of_eventuallyEq
      (Filter.eventually_of_mem (Ioo_mem_nhds hx1 hx2) fun t ht => hloc t ht)
  · intro t
    dsimp only
    calc (∑ᶠ n : ℤ, s0 (t + P - (n : ℝ) * P))
        = ∑ᶠ n : ℤ, s0 (t - (((n - 1 : ℤ)) : ℝ) * P) :=
          finsum_congr fun n => by congr 1; push_cast; ring
      _ = ∑ᶠ n : ℤ, s0 (t - (n : ℝ) * P) :=
          finsum_comp_equiv (Equiv.subRight (1 : ℤ)) (f := fun n : ℤ => s0 (t - (n : ℝ) * P))
  · intro t ht
    dsimp only
    have hzero : ∀ n : ℤ, n ≠ 0 → s0 (t - (n : ℝ) * P) = 0 := by
      intro n hn
      apply image_eq_zero_of_notMem_tsupport
      intro h
      obtain ⟨h0, h1⟩ := hsupp h
      obtain ⟨t0, t1⟩ := ht
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
        linarith [mul_le_mul_of_nonneg_right hn' hP.le]
      · have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
        linarith [mul_le_mul_of_nonneg_right hn' hP.le]
    refine (finsum_eq_single (fun n : ℤ => s0 (t - (n : ℝ) * P)) 0 hzero).trans ?_
    simp

end UnforcedLeray.Short.PartIIIb.Concrete
