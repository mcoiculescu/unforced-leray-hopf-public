import UnforcedLeray.Short.PartI.Sub.T02_2_3

/-!
# Part I, task `PartI:T02/2/3`, leaf `PbRealAvgLimit`: averages over shrinking intervals

Source of record: `the November 2 reference manuscript`, line 447 (the limit step).

Target: `pbRealAvgLimit : PbRealAvgLimit` (the definition is in `Sub/T02_2_3.lean`).  If `Φ` is
continuous on `[0,T]` (`T > 0`) and every interval average `(b-a)⁻¹ ∫_a^b Φ`, `0 ≤ a < b ≤ T`, has
modulus at most `M`, then `|Φ s| ≤ M` for every `s ∈ [0,T]`.

Proof.  Fix `s` and `ε > 0`.  Continuity of `Φ` within `[0,T]` at `s` gives `δ > 0` with
`|Φ x - Φ s| < ε` for `x ∈ [0,T]`, `|x - s| < δ`.  Choose `(a, b]` inside `[0,T]` near `s` with
`a < b` (`pbRA_interval`).  Then `(b-a)⁻¹ ∫_a^b Φ = Φ s + (b-a)⁻¹ ∫_a^b (Φ - Φ s)`, and the last
term has modulus at most `ε`, so `|Φ s| ≤ M + ε`.  Since `ε > 0` is arbitrary, `|Φ s| ≤ M`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

/-- A short interval `(a, b]` inside `[0,T]` all of whose points are within `δ` of a point
`s ∈ [0,T]`: at `s = T` it is `(T - δ/2, T]`, and otherwise `(s, min (s + δ/2) T]`. -/
theorem pbRA_interval (T δ : ℝ) (hT : 0 < T) (hδ : 0 < δ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    ∃ a b : ℝ, a ∈ Icc (0 : ℝ) T ∧ b ∈ Icc (0 : ℝ) T ∧ a < b ∧ ∀ x ∈ Ioc a b, dist x s < δ := by
  rcases eq_or_lt_of_le hs.2 with h | h
  · refine ⟨max (T - δ / 2) 0, T, ⟨le_max_right _ _, max_le (by linarith) hT.le⟩,
      ⟨hT.le, le_rfl⟩, max_lt (by linarith) hT, ?_⟩
    intro x hx
    have h1 := le_max_left (T - δ / 2) 0
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  · refine ⟨s, min (s + δ / 2) T, hs, ⟨le_min (by linarith [hs.1]) hT.le, min_le_right _ _⟩,
      lt_min (by linarith) h, ?_⟩
    intro x hx
    have h1 := min_le_left (s + δ / 2) T
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]

/-- **Averages over shrinking intervals** (leaf of `PbAvgLimit`; pure real analysis). -/
theorem pbRealAvgLimit : PbRealAvgLimit := by
  unfold PbRealAvgLimit
  intro T M Φ hT hΦ havg s hs
  have key : ∀ ε : ℝ, 0 < ε → |Φ s| ≤ M + ε := by
    intro ε hε
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.mp (hΦ s hs) ε hε
    obtain ⟨a, b, ha, hb, hab, hsub⟩ := pbRA_interval T δ hT hδ s hs
    have hdpos : 0 < b - a := sub_pos.mpr hab
    have hd : b - a ≠ 0 := ne_of_gt hdpos
    have hint : IntervalIntegrable Φ volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hab.le]
      exact hΦ.mono (Icc_subset_Icc ha.1 hb.2)
    have hsplit : ∫ σ in a..b, (Φ σ - Φ s) = (∫ σ in a..b, Φ σ) - (b - a) * Φ s := by
      have h2 := intervalIntegral.integral_sub hint
        (intervalIntegrable_const : IntervalIntegrable (fun _ => Φ s) volume a b)
      simp only [intervalIntegral.integral_const, smul_eq_mul] at h2
      exact h2
    have hJ : ‖∫ σ in a..b, (Φ σ - Φ s)‖ ≤ ε * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le hab.le] at hx
      have hxI : x ∈ Icc (0 : ℝ) T := ⟨le_trans ha.1 (le_of_lt hx.1), le_trans hx.2 hb.2⟩
      have hdist := hcont hxI (hsub x hx)
      show ‖Φ x - Φ s‖ ≤ ε
      rw [← dist_eq_norm]
      exact hdist.le
    rw [Real.norm_eq_abs, abs_of_pos hdpos] at hJ
    have hB : |(b - a)⁻¹ * ∫ σ in a..b, (Φ σ - Φ s)| ≤ ε := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hdpos)]
      calc (b - a)⁻¹ * |∫ σ in a..b, (Φ σ - Φ s)| ≤ (b - a)⁻¹ * (ε * (b - a)) :=
            mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hdpos.le)
        _ = ε := by rw [mul_comm ε, inv_mul_cancel_left₀ hd]
    have hcancel : (b - a)⁻¹ * (∫ σ in a..b, Φ σ)
        - (b - a)⁻¹ * (∫ σ in a..b, (Φ σ - Φ s)) = Φ s := by
      linear_combination (-(b - a)⁻¹) * hsplit + Φ s * inv_mul_cancel₀ hd
    have hA := havg a ha b hb hab
    rw [abs_le] at hA hB ⊢
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hcancel]
  by_contra hcon
  rw [not_le] at hcon
  have h := key ((|Φ s| - M) / 2) (by linarith)
  linarith

end UnforcedLeray.Short.PartI
