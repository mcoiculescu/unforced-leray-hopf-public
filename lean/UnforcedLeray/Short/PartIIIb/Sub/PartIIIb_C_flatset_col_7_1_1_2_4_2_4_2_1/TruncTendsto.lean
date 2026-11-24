import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.LerayModeBound

/-!
# `TruncTendsto` (organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/17`)

Source of record `the November 2 reference manuscript`
lines 1744-1747. The finite Fourier sums `Σ_{0<|n|≤N} e_n (-∂_ηψ_n, i k_n ψ_n)` (equal to the sum over
`Icc (-N) N`, the zero term vanishing) converge pointwise to the summable series `lerayTail c f`, by
the uniform summable bound `C/(1+n²)` of `LerayModeBound` and `|e_n| = 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

theorem tt_eN_norm (c : ℝ) (n : ℤ) (q : ℝ) : ‖eN c n q‖ = 1 := by
  have h : eN c n q = Complex.exp (((2 * Real.pi * n * q / c : ℝ) : ℂ) * Complex.I) := by
    unfold eN
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem tt_summable_bound (C : ℝ) : Summable (fun n : ℤ => C / (1 + (n : ℝ) ^ 2)) := by
  have h1 : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.2 (by norm_num)
  have h2 : Summable (fun n : ℤ => 1 / (1 + (n : ℝ) ^ 2)) := by
    refine Summable.of_norm_bounded_eventually h1 ?_
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hpos : 0 < (n : ℝ) ^ 2 := by positivity
    show ‖1 / (1 + (n : ℝ) ^ 2)‖ ≤ 1 / (n : ℝ) ^ 2
    rw [Real.norm_of_nonneg (by positivity)]
    exact one_div_le_one_div_of_le hpos (by linarith)
  exact (h2.mul_left C).congr (fun n => by ring)

theorem truncTendsto : TruncTendsto := by
  intro c hc f hf p
  obtain ⟨C, hC⟩ := lerayModeBound c hc f hf
  have hsum : Summable (fun n : ℤ => eN c n p.2.1 • lerayMode c f n (p.1, p.2.2)) :=
    Summable.of_norm_bounded (tt_summable_bound C) (fun n => by
      rw [norm_smul, tt_eN_norm, one_mul]
      exact hC n (p.1, p.2.2))
  have hS : HasSum (fun n : ℤ => eN c n p.2.1 • lerayMode c f n (p.1, p.2.2))
      (lerayTail c f p) :=
    hsum.hasSum
  have hmono : Monotone (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
    intro a b hab
    have h : ((a : ℕ) : ℤ) ≤ ((b : ℕ) : ℤ) := by exact_mod_cast hab
    exact Finset.Icc_subset_Icc (neg_le_neg h) h
  have hcov : ∀ x : ℤ, ∃ N : ℕ, x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := fun x =>
    ⟨x.natAbs, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩
  have hT : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop :=
    tendsto_atTop_finset_of_monotone hmono hcov
  have hS' : Tendsto (fun s : Finset ℤ => ∑ b ∈ s, eN c b p.2.1 • lerayMode c f b (p.1, p.2.2))
      atTop (𝓝 (lerayTail c f p)) := hS
  have hlim : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      eN c n p.2.1 • lerayMode c f n (p.1, p.2.2)) atTop (𝓝 (lerayTail c f p)) :=
    hS'.comp hT
  have h0 : eN c 0 p.2.1 • lerayMode c f 0 (p.1, p.2.2) = 0 := by
    simp [lerayMode]
  refine Tendsto.congr (fun N => ?_) hlim
  unfold lerayTrunc truncSet
  rw [Finset.sum_erase (f := fun n : ℤ => eN c n p.2.1 • lerayMode c f n (p.1, p.2.2)) (a := 0)
    (Finset.Icc (-(N : ℤ)) (N : ℤ)) h0]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
