import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2

/-!
# `PartIII-b:C/ward/13/8/2/3`: the dyadic drift lemma (pure real analysis)

Statement `DyadicDrift` from `Sub/PartIII-b_C_ward_13_8_2.lean`. Proof: with `r = 2^(-1/2)`,
the increments satisfy `|m_{k+1} - m_k| ≤ |K| r^k √(E_k)`, which is summable, so `m_k → c`.
The tail estimate `|m_k - c| ≤ |K| B r^k / (1 - r)` once `√(E_j) ≤ B` for `j ≥ k` gives
`2^{k/2} |m_k - c| → 0` by an `ε`-argument.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem dyadicDrift : DyadicDrift := by
  intro m E K hE0 hElim hm
  set r : ℝ := (2:ℝ) ^ (-(1:ℝ)/2) with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hr1' : (1 - r) ≠ 0 := (sub_pos.mpr hr1).ne'
  have hpow : ∀ j : ℕ, (2:ℝ) ^ (-(j:ℝ)/2) = r ^ j := by
    intro j
    rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hw : ∀ k : ℕ, (2:ℝ) ^ ((k:ℝ)/2) * r ^ k = 1 := by
    intro k
    rw [← hpow k, ← Real.rpow_add (by norm_num), show (k:ℝ)/2 + -(k:ℝ)/2 = 0 by ring,
      Real.rpow_zero]
  have hstep : ∀ k : ℕ, |m (k+1) - m k| ≤ |K| * r ^ k * Real.sqrt (E k) := by
    intro k
    have h := hm k
    rw [hpow k] at h
    refine h.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
  obtain ⟨M, hM⟩ : ∃ M, ∀ k, E k ≤ M := by
    obtain ⟨M, hM⟩ := hElim.bddAbove_range
    exact ⟨M, fun k => hM ⟨k, rfl⟩⟩
  have hsum : Summable (fun k : ℕ => dist (m k) (m (k+1))) := by
    refine Summable.of_nonneg_of_le (fun k => dist_nonneg) (fun k => ?_)
      ((summable_geometric_of_lt_one hr0.le hr1).mul_left (|K| * Real.sqrt M))
    rw [Real.dist_eq, abs_sub_comm]
    refine (hstep k).trans ?_
    have hs : Real.sqrt (E k) ≤ Real.sqrt M := Real.sqrt_le_sqrt (hM k)
    have hr : 0 ≤ r ^ k := by positivity
    calc |K| * r ^ k * Real.sqrt (E k) ≤ |K| * r ^ k * Real.sqrt M := by gcongr
      _ = |K| * Real.sqrt M * r ^ k := by ring
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)
  have hgeom : ∀ (k : ℕ) (B : ℝ), 0 ≤ B → (∀ j, k ≤ j → Real.sqrt (E j) ≤ B) →
      |m k - c| ≤ |K| * B * r ^ k / (1 - r) := by
    intro k B hB hEB
    have hind : ∀ n : ℕ, |m (k+n) - m k| ≤ |K| * B * r ^ k * (1 - r ^ n) / (1 - r) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        show |m (k+n+1) - m k| ≤ _
        have hs := hstep (k+n)
        have hEn : Real.sqrt (E (k+n)) ≤ B := hEB (k+n) (by omega)
        have h2 : |K| * r ^ (k+n) * Real.sqrt (E (k+n)) ≤ |K| * B * r ^ (k+n) := by
          have : 0 ≤ |K| * r ^ (k+n) := by positivity
          nlinarith
        have key : |K| * B * r ^ k * (1 - r ^ n) / (1 - r) + |K| * B * r ^ (k+n)
            = |K| * B * r ^ k * (1 - r ^ (n+1)) / (1 - r) := by
          rw [pow_add, pow_succ]
          field_simp
          ring
        calc |m (k+n+1) - m k|
            = |(m (k+n+1) - m (k+n)) + (m (k+n) - m k)| := by ring_nf
          _ ≤ |m (k+n+1) - m (k+n)| + |m (k+n) - m k| := abs_add_le _ _
          _ ≤ |K| * B * r ^ (k+n) + |K| * B * r ^ k * (1 - r ^ n) / (1 - r) :=
              add_le_add (hs.trans h2) ih
          _ = |K| * B * r ^ k * (1 - r ^ (n+1)) / (1 - r) := by linarith [key]
    have hlim : Tendsto (fun n : ℕ => |m (k+n) - m k|) atTop (𝓝 |c - m k|) := by
      have hk : Tendsto (fun n : ℕ => k + n) atTop atTop :=
        tendsto_atTop_mono (fun n => Nat.le_add_left n k) tendsto_id
      have hmk : Tendsto (fun n : ℕ => m (k+n)) atTop (𝓝 c) := hc.comp hk
      exact ((hmk.sub_const (m k)).abs)
    have hbound : ∀ n : ℕ, |m (k+n) - m k| ≤ |K| * B * r ^ k / (1 - r) := by
      intro n
      refine (hind n).trans ?_
      have h1 : 1 - r ^ n ≤ 1 := by linarith [pow_nonneg hr0.le n]
      have h2 : 0 ≤ |K| * B * r ^ k := by positivity
      have h3 : 0 < 1 - r := by linarith
      apply div_le_div_of_nonneg_right _ h3.le
      nlinarith [mul_le_mul_of_nonneg_left h1 h2]
    rw [abs_sub_comm]
    exact le_of_tendsto hlim (Eventually.of_forall hbound)
  have hsq : Tendsto (fun j => Real.sqrt (E j)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hElim
    rw [Real.sqrt_zero] at h
    exact h
  refine ⟨c, Metric.tendsto_nhds.2 fun ε hε => ?_⟩
  have hB : 0 < ε * (1 - r) / (2 * (|K| + 1)) :=
    div_pos (mul_pos hε (by linarith)) (by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hsq.eventually (gt_mem_nhds hB))
  refine Filter.eventually_atTop.2 ⟨N, fun k hk => ?_⟩
  have hbd := hgeom k (ε * (1 - r) / (2 * (|K| + 1))) hB.le
    (fun j hj => (hN j (le_trans hk hj)).le)
  have hnn : 0 ≤ (2:ℝ) ^ ((k:ℝ)/2) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hnn (abs_nonneg _))]
  have hfac : (2:ℝ) ^ ((k:ℝ)/2) * (|K| * (ε * (1 - r) / (2 * (|K| + 1))) * r ^ k / (1 - r))
      = (|K| * (ε * (1 - r) / (2 * (|K| + 1))) / (1 - r)) * ((2:ℝ) ^ ((k:ℝ)/2) * r ^ k) := by
    ring
  have hval : |K| * (ε * (1 - r) / (2 * (|K| + 1))) / (1 - r) = |K| * ε / (2 * (|K| + 1)) := by
    field_simp
  have hlt : |K| * ε / (2 * (|K| + 1)) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg K]
  calc (2:ℝ) ^ ((k:ℝ)/2) * |m k - c|
      ≤ (2:ℝ) ^ ((k:ℝ)/2) * (|K| * (ε * (1 - r) / (2 * (|K| + 1))) * r ^ k / (1 - r)) :=
        mul_le_mul_of_nonneg_left hbd hnn
    _ = |K| * ε / (2 * (|K| + 1)) := by rw [hfac, hw k, mul_one, hval]
    _ < ε := hlt

end UnforcedLeray.Short.PartIIIb.Concrete
