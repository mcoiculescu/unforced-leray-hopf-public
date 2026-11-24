import UnforcedLeray.Short.Spine.Sub.SP_CAN4_1

/-!
# Leaf 1: `XGjIntervalIntegralMem` (task `Spine:SP-CAN/4/1`)

Proves `UnforcedLeray.Short.Spine.XGjIntervalIntegralMem` (`Sub/SP_CAN4_1.lean`); the statement is
not changed.

Route. For `N : ℕ` let `T N : X_G →L[ℂ] EuclideanSpace ℂ (Fin (N+1))` send `x` to
`(√(1 + (1+n)^j) ⟪e_n, x⟫)_{n ≤ N}`, so `‖T N x‖² = ∑_{n ≤ N} (1 + (1+n)^j) ‖⟪e_n, x⟫‖²`.
For `x ∈ X_{G,j}` this is at most `xgjNorm j x ^ 2` (partial sums of `B0123.hasSum_xgjNorm_sq`).
So `‖T N (F u)‖ ≤ G u` for a.e. `u ∈ Ioc a b`, and `ContinuousLinearMap.intervalIntegral_comp_comm`
with `intervalIntegral.norm_integral_le_of_norm_le` gives `‖T N (∫ F)‖ ≤ ∫ G` for every `N`.
Hence every partial sum of `∑ (1 + (1+n)^j) ‖⟪e_n, ∫ F⟫‖²` is at most `(∫ G)²`. This gives
summability, membership in `X_{G,j}` (`B0123.mem_XGj_iff`) and the norm bound
(`B0123.hasSum_xgjNorm_sq`). No measurability of `u ↦ xgjNorm j (F u)` is used.

Source of record: `the November 2 reference manuscript`, lines 1086 and 1134-1145.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- `XGjIntervalIntegralMem` holds: the Bochner integral of an `X_G`-valued function with values
in `X_{G,j}` and a majorant of the `X_{G,j}` graph norm stays in `X_{G,j}`, with the bound. -/
theorem xgjIntervalIntegralMem_proof : UnforcedLeray.Short.Spine.XGjIntervalIntegralMem := by
  intro j F G a b hab hF hG hmaj
  -- finite truncations `T N : X_G → ℓ²_{N+1}` with the weighted-sum norm identity
  have hT : ∀ N : ℕ, ∃ T : XG →L[ℂ] EuclideanSpace ℂ (Fin (N + 1)), ∀ x : XG,
      ‖T x‖ ^ 2 = ∑ n ∈ Finset.range (N + 1),
        (1 + (1 + (n : ℝ)) ^ j) * ‖inner ℂ (B0094.oscBasis n) x‖ ^ 2 := by
    intro N
    refine ⟨(EuclideanSpace.equiv (Fin (N + 1)) ℂ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i : Fin (N + 1) =>
        ((Real.sqrt (1 + (1 + ((i : ℕ) : ℝ)) ^ j) : ℝ) : ℂ) •
          innerSL ℂ (B0094.oscBasis (i : ℕ))), fun x => ?_⟩
    rw [EuclideanSpace.norm_sq_eq, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hw : (0 : ℝ) ≤ 1 + (1 + ((i : ℕ) : ℝ)) ^ j := by positivity
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      PiLp.coe_symm_continuousLinearEquiv, PiLp.toLp_apply, ContinuousLinearMap.pi_apply,
      smul_apply, innerSL_apply_apply, smul_eq_mul]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hw]
  choose T hTsq using hT
  -- pointwise: `‖T N x‖ ≤ xgjNorm j x` for `x ∈ X_{G,j}`
  have hpoint : ∀ (N : ℕ) (x : XG) (h : x ∈ B0123.XGj j),
      ‖T N x‖ ≤ B0123.xgjNorm j ⟨x, h⟩ := by
    intro N x h
    have hs := sum_le_hasSum (Finset.range (N + 1))
      (fun n _ => by positivity) (B0123.hasSum_xgjNorm_sq j ⟨x, h⟩)
    have hsq : ‖T N x‖ ^ 2 ≤ B0123.xgjNorm j ⟨x, h⟩ ^ 2 := by
      rw [hTsq N x]
      exact hs
    have hx : 0 ≤ B0123.xgjNorm j ⟨x, h⟩ := B0123.xgjNorm_nonneg j ⟨x, h⟩
    nlinarith [norm_nonneg (T N x)]
  -- the integral of `T N ∘ F` is majorised by `∫ G`
  have hmajT : ∀ N : ℕ, ‖T N (∫ u in a..b, F u)‖ ≤ ∫ u in a..b, G u := by
    intro N
    rw [← (T N).intervalIntegral_comp_comm hF]
    refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ hG
    filter_upwards [hmaj] with u hu hIoc
    obtain ⟨h, hle⟩ := hu hIoc
    exact (hpoint N (F u) h).trans hle
  have hM0 : 0 ≤ ∫ u in a..b, G u := (norm_nonneg _).trans (hmajT 0)
  -- partial sums of the weighted coefficient series of `∫ F` are at most `(∫ G)²`
  have hpart : ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (1 + (1 + (i : ℝ)) ^ j) * ‖inner ℂ (B0094.oscBasis i) (∫ u in a..b, F u)‖ ^ 2
        ≤ (∫ u in a..b, G u) ^ 2 := by
    intro n
    rcases n with _ | N
    · rw [Finset.sum_range_zero]
      positivity
    · rw [← hTsq N (∫ u in a..b, F u)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hmajT N) 2
  have hsumm : Summable fun n : ℕ =>
      (1 + (1 + (n : ℝ)) ^ j) * ‖inner ℂ (B0094.oscBasis n) (∫ u in a..b, F u)‖ ^ 2 :=
    summable_of_sum_range_le (fun n => by positivity) hpart
  -- membership in `X_{G,j}`: compare with the weighted series
  have hmem : (∫ u in a..b, F u) ∈ B0123.XGj j := by
    rw [B0123.mem_XGj_iff]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsumm
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  refine ⟨hmem, ?_⟩
  have hsum := B0123.hasSum_xgjNorm_sq j ⟨∫ u in a..b, F u, hmem⟩
  have hle : B0123.xgjNorm j ⟨∫ u in a..b, F u, hmem⟩ ^ 2 ≤ (∫ u in a..b, G u) ^ 2 := by
    rw [← hsum.tsum_eq]
    exact Real.tsum_le_of_sum_range_le (fun n => by positivity) hpart
  have hX : 0 ≤ B0123.xgjNorm j ⟨∫ u in a..b, F u, hmem⟩ := B0123.xgjNorm_nonneg j _
  nlinarith [hle, hX, hM0]

end UnforcedLeray.Short.Spine
