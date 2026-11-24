import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_1

/-!
# Part III-a, task `PartIII-a:T18/3/1/1/8`: the cutoff family `u_k(η) = χ(η/(k+1))`

Target (`Sub/T18_3_1_1.lean`): `DfcScaledExists`. Source of record:
`the November 2 reference manuscript`, lines 3541-3552 (cutoff of the density
argument); the stream-function argument is recorded in the docstring of `Sub/T18_3_1_1.lean`.

## Mathematics

Let `b` be the `ContDiffBump` at `0` with `rIn = 1`, `rOut = 2`, so `b` is smooth, `0 ≤ b ≤ 1`,
`b = 1` on `[-1, 1]` and `b = 0` off `(-2, 2)`. Put `u k t = b (t / (k+1))`, with `c = k+1 ≥ 1`.

* `u k t = 0` when `2 (k+1) < |t|`, since then `|t / c| > 2`; the same holds for the derivative,
  as `u k` vanishes on the open set `{|s| > 2 (k+1)}` containing `t`.
* Chain rule: `u_k'(t) = b'(t/c) / c` and `u_k''(t) = b''(t/c) / c²`.
* `b'`, `b''` are continuous with compact support, hence bounded by `C1`, `C2`; since `1/c ≤ 1`,
  `|u_k'| ≤ C1 / c` and `|u_k''| ≤ C2 / c ≤ C2`.
* `u_k(t) = 1` once `k + 1 ≥ |t|`; `u_k' → 0` and `u_k'' → 0` pointwise since `1/c → 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem dfcScaledExists : UnforcedLeray.Short.IIIa.DfcScaledExists := by
  unfold UnforcedLeray.Short.IIIa.DfcScaledExists
  -- the bump function with radii `1` and `2`
  obtain ⟨b, hb1, hb2⟩ : ∃ b : ContDiffBump (0:ℝ), b.rIn = 1 ∧ b.rOut = 2 :=
    ⟨⟨1, 2, one_pos, one_lt_two⟩, rfl, rfl⟩
  have hbC : ContDiff ℝ ∞ (⇑b) := b.contDiff
  have hbcs : HasCompactSupport (⇑b) := b.hasCompactSupport
  have hbdiff : Differentiable ℝ (⇑b) := hbC.differentiable (by simp)
  have hdbC : ContDiff ℝ ∞ (deriv (⇑b)) := (contDiff_infty_iff_deriv.mp hbC).2
  have hdbdiff : Differentiable ℝ (deriv (⇑b)) := hdbC.differentiable (by simp)
  have hddbC : ContDiff ℝ ∞ (deriv (deriv (⇑b))) := (contDiff_infty_iff_deriv.mp hdbC).2
  have hbcs1 : HasCompactSupport (deriv (⇑b)) := hbcs.deriv
  have hbcs2 : HasCompactSupport (deriv (deriv (⇑b))) := hbcs1.deriv
  obtain ⟨C1, hC1⟩ := hdbC.continuous.bounded_above_of_compact_support hbcs1
  obtain ⟨C2, hC2⟩ := hddbC.continuous.bounded_above_of_compact_support hbcs2
  have hC1nn : 0 ≤ C1 := le_trans (norm_nonneg _) (hC1 0)
  have hC2nn : 0 ≤ C2 := le_trans (norm_nonneg _) (hC2 0)
  -- values of the bump
  have hzero : ∀ t : ℝ, 2 ≤ |t| → b t = 0 := by
    intro t ht
    apply b.zero_of_le_dist
    rw [hb2, Real.dist_eq, sub_zero]
    exact ht
  have hone : ∀ t : ℝ, |t| ≤ 1 → b t = 1 := by
    intro t ht
    apply b.one_of_mem_closedBall
    rw [hb1, Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact ht
  -- the cutoff family
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ → ℝ, ∀ k t, u k t = b (t / ((k:ℝ) + 1)) :=
    ⟨fun k t => b (t / ((k:ℝ) + 1)), fun _ _ => rfl⟩
  have hu_fun : ∀ k : ℕ, u k = fun t => b (t / ((k:ℝ) + 1)) := fun k => funext (hu k)
  have hpos : ∀ k : ℕ, (0:ℝ) < (k:ℝ) + 1 := fun k => by positivity
  have hinv : ∀ k : ℕ, 0 < 1 / ((k:ℝ) + 1) ∧ 1 / ((k:ℝ) + 1) ≤ 1 := by
    intro k
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (hpos k)]
    have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  -- derivatives by the chain rule
  have hd1 : ∀ (k : ℕ) (t : ℝ),
      HasDerivAt (u k) (deriv (⇑b) (t / ((k:ℝ) + 1)) * (1 / ((k:ℝ) + 1))) t := by
    intro k t
    rw [hu_fun k]
    have hin : HasDerivAt (fun s : ℝ => s / ((k:ℝ) + 1)) (1 / ((k:ℝ) + 1)) t :=
      (hasDerivAt_id' t).div_const _
    have key := (hbdiff (t / ((k:ℝ) + 1))).hasDerivAt.comp t hin
    exact key
  have hdu : ∀ k : ℕ, deriv (u k) =
      fun s => deriv (⇑b) (s / ((k:ℝ) + 1)) * (1 / ((k:ℝ) + 1)) :=
    fun k => funext fun t => (hd1 k t).deriv
  have hd2 : ∀ (k : ℕ) (t : ℝ), HasDerivAt (deriv (u k))
      (deriv (deriv (⇑b)) (t / ((k:ℝ) + 1)) * (1 / ((k:ℝ) + 1)) * (1 / ((k:ℝ) + 1))) t := by
    intro k t
    rw [hdu k]
    have hin : HasDerivAt (fun s : ℝ => s / ((k:ℝ) + 1)) (1 / ((k:ℝ) + 1)) t :=
      (hasDerivAt_id' t).div_const _
    exact ((hdbdiff (t / ((k:ℝ) + 1))).hasDerivAt.comp t hin).mul_const _
  have hdd : ∀ (k : ℕ) (t : ℝ), deriv (deriv (u k)) t =
      deriv (deriv (⇑b)) (t / ((k:ℝ) + 1)) * (1 / ((k:ℝ) + 1)) * (1 / ((k:ℝ) + 1)) :=
    fun k t => (hd2 k t).deriv
  -- pointwise bounds on the derivatives, with the decay `1 / (k+1)`
  have hD1 : ∀ (k : ℕ) (t : ℝ), |deriv (u k) t| ≤ C1 * (1 / ((k:ℝ) + 1)) := by
    intro k t
    have h := hC1 (t / ((k:ℝ) + 1))
    rw [Real.norm_eq_abs] at h
    rw [(hd1 k t).deriv, abs_mul, abs_of_pos (hinv k).1]
    exact mul_le_mul_of_nonneg_right h (hinv k).1.le
  have hD2 : ∀ (k : ℕ) (t : ℝ), |deriv (deriv (u k)) t| ≤ C2 * (1 / ((k:ℝ) + 1)) := by
    intro k t
    have h := hC2 (t / ((k:ℝ) + 1))
    rw [Real.norm_eq_abs] at h
    rw [hdd k t, abs_mul, abs_mul, abs_of_pos (hinv k).1]
    exact mul_le_mul_of_nonneg_right
      (le_trans (mul_le_of_le_one_right (abs_nonneg _) (hinv k).2) h) (hinv k).1.le
  -- the decaying sequences `C * (1 / (k+1)) → 0`
  have hLim1 : Tendsto (fun k : ℕ => C1 * (1 / ((k:ℝ) + 1))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C1
    rw [mul_zero] at h
    exact h
  have hLim2 : Tendsto (fun k : ℕ => C2 * (1 / ((k:ℝ) + 1))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C2
    rw [mul_zero] at h
    exact h
  refine ⟨u, ?_⟩
  refine ⟨?_, ?_, ?_, ⟨C1, ?_⟩, ⟨C2, ?_⟩, ?_, ?_, ?_⟩
  · -- smoothness
    intro k
    rw [hu_fun k]
    have hin : ContDiff ℝ ∞ (fun s : ℝ => s / ((k:ℝ) + 1)) := contDiff_id.div_const _
    exact hbC.comp hin
  · -- values in `[0, 1]`
    intro k t
    rw [hu k t]
    exact ⟨b.nonneg, b.le_one⟩
  · -- vanishing for `2 (k+1) < |t|`
    intro k t ht
    have hk := hpos k
    have hzk : ∀ s : ℝ, 2 * ((k:ℝ) + 1) < |s| → u k s = 0 := by
      intro s hs
      rw [hu k s]
      apply hzero
      rw [abs_div, abs_of_pos hk]
      exact (le_div_iff₀ hk).2 hs.le
    refine ⟨hzk t ht, ?_⟩
    have hev : u k =ᶠ[nhds t] (fun _ => (0:ℝ)) := by
      have hopen : ∀ᶠ s in nhds t, 2 * ((k:ℝ) + 1) < |s| :=
        (continuous_abs.tendsto t).eventually (lt_mem_nhds ht)
      filter_upwards [hopen] with s hs
      exact hzk s hs
    rw [hev.deriv_eq, deriv_const]
  · -- first derivatives are uniformly bounded
    intro k t
    exact le_trans (hD1 k t) (mul_le_of_le_one_right hC1nn (hinv k).2)
  · -- second derivatives are uniformly bounded
    intro k t
    exact le_trans (hD2 k t) (mul_le_of_le_one_right hC2nn (hinv k).2)
  · -- `u_k(t) = 1` once `k + 1 ≥ |t|`
    intro t
    obtain ⟨N, hN⟩ := exists_nat_ge |t|
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    have hk' : (N:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    rw [hu k t]
    apply hone
    rw [abs_div, abs_of_pos (hpos k), div_le_one (hpos k)]
    linarith
  · -- `u_k' → 0` pointwise
    intro t
    refine squeeze_zero_norm (fun k => ?_) hLim1
    show ‖deriv (u k) t‖ ≤ C1 * (1 / ((k:ℝ) + 1))
    rw [Real.norm_eq_abs]
    exact hD1 k t
  · -- `u_k'' → 0` pointwise
    intro t
    refine squeeze_zero_norm (fun k => ?_) hLim2
    show ‖deriv (deriv (u k)) t‖ ≤ C2 * (1 / ((k:ℝ) + 1))
    rw [Real.norm_eq_abs]
    exact hD2 k t

end UnforcedLeray.Short.IIIa
