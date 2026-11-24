import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.PSeries

/-!
# Spine: `SeriesIdentify` (leaf 4 of `Spine:SP-CAN/4/4`)

Proves `SeriesIdentify` (`Short/Spine/Sub/SP_CAN4_4.lean`) with the statement unchanged.

Source of record: `the November 2 reference manuscript` lines 1086 and 1134-1140.

Route.

1. For `r > 0`, put `c n = ⟪e_n, f⟫`. Membership of `f` in `X_{G,2q+4}` gives
   `∑ (1+n)^(2q+4) |c n|² < ∞`. The algebraic bound `x t^q ≤ t^(2q+4) x² + t^(-2)` (with `t ≥ 1`)
   then gives `∑ |c n| (1+n)^q < ∞`, so `∑ c n φ_n r` is absolutely summable at `r`.
2. The Hilbert basis expansion `∑ c n e_n → f` holds in `XG`, hence in measure; a subsequence of
   the partial sums converges a.e. to `f`.
3. The partial sums of `∑ c n φ_n r` converge at every `r > 0` to the series value. Uniqueness of
   limits gives equality a.e., and `ae_xG_pos` restricts to `r > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- Algebraic bound: for `t ≥ 1` and `x ≥ 0`, `x t^q ≤ t^(2q+4) x² + t^(-2)`. -/
theorem amgm_weight_aux (q : ℕ) (t x : ℝ) (ht : 1 ≤ t) :
    x * t ^ q ≤ t ^ (2 * q + 4) * x ^ 2 + 1 / t ^ 2 := by
  have htpos : 0 < t := by linarith
  have hb : (0 : ℝ) ≤ 1 / t ^ 2 := by positivity
  have hb1 : 1 / t ^ 2 ≤ 1 := by
    rw [div_le_one (pow_pos htpos 2)]
    nlinarith
  have hab : (t ^ (q + 2) * x) * (1 / t ^ 2) = x * t ^ q := by
    rw [mul_one_div, div_eq_iff (pow_ne_zero 2 htpos.ne')]
    ring
  have hsq : t ^ (2 * q + 4) * x ^ 2 = (t ^ (q + 2) * x) ^ 2 := by ring
  rw [← hab, hsq]
  nlinarith [sq_nonneg (t ^ (q + 2) * x - 1 / t ^ 2), sq_nonneg (t ^ (q + 2) * x),
    mul_nonneg hb (sub_nonneg.2 hb1)]

/-- Summability of `∑ ‖c n‖ (1+n)^q` from summability of `(1+n)^(2q+4) ‖c n‖²`. -/
theorem summable_norm_mul_pow_aux (c : ℕ → ℂ) (q : ℕ)
    (hc : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ (2 * q + 4) * ‖c n‖ ^ 2)) :
    Summable (fun n : ℕ => ‖c n‖ * (1 + (n : ℝ)) ^ q) := by
  have hw : Summable (fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 2) := by
    have h : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num))
    refine h.congr (fun n => ?_)
    push_cast
    ring
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hc.add hw)
  · show 0 ≤ ‖c n‖ * (1 + (n : ℝ)) ^ q
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith) _)
  · show ‖c n‖ * (1 + (n : ℝ)) ^ q ≤ (1 + (n : ℝ)) ^ (2 * q + 4) * ‖c n‖ ^ 2 + 1 / (1 + (n : ℝ)) ^ 2
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact amgm_weight_aux q (1 + (n : ℝ)) ‖c n‖ (by linarith)

/-- **Leaf 4, the expansion identifies the representative** (Hilbert-basis level). Statement
`SeriesIdentify` from `Sub/SP_CAN4_4.lean`, proved as stated. -/
theorem seriesIdentify_proof : SeriesIdentify := by
  intro φ f hφae hφbd hfj
  -- Step 1: absolute summability of `∑ ⟪e_n, f⟫ φ_n(r)` at each `r > 0`.
  have hsum_pt : ∀ r : ℝ, 0 < r →
      Summable (fun n : ℕ => inner ℂ (UnforcedLeray.B0094.oscBasis n) f * φ n r) := by
    intro r hr
    obtain ⟨C, q, hC⟩ := hφbd (r / 2) (r + 1) (by linarith) (by linarith)
    have hr_mem : r ∈ Icc (r / 2) (r + 1) := ⟨by linarith, by linarith⟩
    have hX : Summable (fun n : ℕ =>
        (1 + (n : ℝ)) ^ (2 * q + 4) * ‖inner ℂ (UnforcedLeray.B0094.oscBasis n) f‖ ^ 2) :=
      (UnforcedLeray.B0123.mem_XGj_iff (2 * q + 4) f).1 (hfj (2 * q + 4))
    have hA : Summable (fun n : ℕ =>
        ‖inner ℂ (UnforcedLeray.B0094.oscBasis n) f‖ * (1 + (n : ℝ)) ^ q) :=
      summable_norm_mul_pow_aux (fun n => inner ℂ (UnforcedLeray.B0094.oscBasis n) f) q hX
    have hg : Summable (fun n : ℕ =>
        C * (‖inner ℂ (UnforcedLeray.B0094.oscBasis n) f‖ * (1 + (n : ℝ)) ^ q)) :=
      hA.mul_left C
    have hbd : ∀ n : ℕ, ‖inner ℂ (UnforcedLeray.B0094.oscBasis n) f * φ n r‖ ≤
        C * (‖inner ℂ (UnforcedLeray.B0094.oscBasis n) f‖ * (1 + (n : ℝ)) ^ q) := by
      intro n
      calc ‖inner ℂ (UnforcedLeray.B0094.oscBasis n) f * φ n r‖
          = ‖inner ℂ (UnforcedLeray.B0094.oscBasis n) f‖ * ‖φ n r‖ := norm_mul _ _
        _ ≤ ‖inner ℂ (UnforcedLeray.B0094.oscBasis n) f‖ * (C * (1 + (n : ℝ)) ^ q) :=
            mul_le_mul_of_nonneg_left (hC n r hr_mem) (norm_nonneg _)
        _ = C * (‖inner ℂ (UnforcedLeray.B0094.oscBasis n) f‖ * (1 + (n : ℝ)) ^ q) := by ring
    exact Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbd hg)
  -- Step 2: the Hilbert basis expansion of `f` converges to `f` in `XG`.
  have hS : HasSum (fun n : ℕ => inner ℂ (UnforcedLeray.B0094.oscBasis n) f •
      UnforcedLeray.B0094.oscBasis n) f := by
    have h := UnforcedLeray.B0094.oscBasis.hasSum_repr f
    simpa only [HilbertBasis.repr_apply_apply] using h
  have hpartial : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      inner ℂ (UnforcedLeray.B0094.oscBasis n) f • UnforcedLeray.B0094.oscBasis n) atTop
      (𝓝 f) :=
    hS.tendsto_sum_nat
  -- Step 3: the partial sums as functions agree a.e. with the scalar partial sums.
  have hcoe : ∀ N : ℕ,
      (⇑(∑ n ∈ Finset.range N,
          inner ℂ (UnforcedLeray.B0094.oscBasis n) f • UnforcedLeray.B0094.oscBasis n) :
          ℝ → ℂ) =ᵐ[xGMeasure]
        (fun r => ∑ n ∈ Finset.range N, inner ℂ (UnforcedLeray.B0094.oscBasis n) f * φ n r) := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact Lp.coeFn_zero ℂ 2 xGMeasure
    | succ N ih =>
      filter_upwards [ih,
        Lp.coeFn_add (∑ n ∈ Finset.range N,
            inner ℂ (UnforcedLeray.B0094.oscBasis n) f • UnforcedLeray.B0094.oscBasis n)
          (inner ℂ (UnforcedLeray.B0094.oscBasis N) f • UnforcedLeray.B0094.oscBasis N),
        Lp.coeFn_smul (inner ℂ (UnforcedLeray.B0094.oscBasis N) f)
          (UnforcedLeray.B0094.oscBasis N),
        hφae N] with r h1 h2 h3 h4
      simp only [Finset.sum_range_succ]
      rw [h2, Pi.add_apply, h1, h3, Pi.smul_apply, smul_eq_mul, h4]
  -- Step 4: convergence in measure, then an a.e. convergent subsequence.
  have hmeas := tendstoInMeasure_of_tendsto_Lp hpartial
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hall : ∀ᵐ r ∂xGMeasure, ∀ N : ℕ,
      (⇑(∑ n ∈ Finset.range N,
          inner ℂ (UnforcedLeray.B0094.oscBasis n) f • UnforcedLeray.B0094.oscBasis n) :
          ℝ → ℂ) r =
        ∑ n ∈ Finset.range N, inner ℂ (UnforcedLeray.B0094.oscBasis n) f * φ n r :=
    ae_all_iff.2 (fun N => hcoe N)
  filter_upwards [hae, hall, UnforcedLeray.B0012.ae_xG_pos] with r hr1 hr2 hr3
  have hlim : Tendsto (fun i : ℕ =>
      ∑ n ∈ Finset.range (ns i), inner ℂ (UnforcedLeray.B0094.oscBasis n) f * φ n r)
      atTop (𝓝 ((f : ℝ → ℂ) r)) :=
    Tendsto.congr (fun i => hr2 (ns i)) hr1
  have hser : Tendsto (fun i : ℕ =>
      ∑ n ∈ Finset.range (ns i), inner ℂ (UnforcedLeray.B0094.oscBasis n) f * φ n r)
      atTop (𝓝 (∑' n : ℕ, inner ℂ (UnforcedLeray.B0094.oscBasis n) f * φ n r)) :=
    (hsum_pt r hr3).hasSum.tendsto_sum_nat.comp hns.tendsto_atTop
  exact tendsto_nhds_unique hser hlim

end UnforcedLeray.Short.Spine
