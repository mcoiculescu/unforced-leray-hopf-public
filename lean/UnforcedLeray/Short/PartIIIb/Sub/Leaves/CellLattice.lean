import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# `PartIII-b:C/inst/9/3` leaf 1b: uniform lattice sum of Gaussian weights (source 5063-5079)

For `c ≥ 1` and `a ∈ [1, 2.1]`, `∑_j exp(-(t - jc)²/(8a))` is bounded uniformly in `t`.
Proof: round `t/c` to the nearest integer `j₀`, so `|t - j₀c| ≤ c/2`; reindex by `k = j - j₀`;
then `|t - (k+j₀)c| ≥ |k|/2` for every `k ∈ ℤ` (trivial for `k = 0`, and `|k| ≥ 1` otherwise),
so each term is at most `exp(-k²/67.2)`, which is summable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fAcLatticeWeight : FAcLatticeWeight := by
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = 1 / (32 * (21 / 10)) := ⟨_, rfl⟩
  have hα : 0 < α := by rw [hαdef]; norm_num
  have hαv : α * (8 * (21 / 10)) = 1 / 4 := by rw [hαdef]; norm_num
  have hS : Summable (fun k : ℤ => Real.exp (-α * (k : ℝ) ^ 2)) := by
    simpa using gp_gauss_summable 0 α 1 hα one_pos
  refine ⟨∑' k : ℤ, Real.exp (-α * (k : ℝ) ^ 2), ?_⟩
  intro c t a hc ha1 ha2
  have hc0 : 0 < c := by linarith
  have ha0 : 0 < a := by linarith
  -- nearest integer to t / c
  set j0 : ℤ := ⌊t / c + 1 / 2⌋ with hj0
  have h1 : (j0 : ℝ) ≤ t / c + 1 / 2 := Int.floor_le _
  have h2 : t / c + 1 / 2 < (j0 : ℝ) + 1 := Int.lt_floor_add_one _
  have hu : |t - (j0 : ℝ) * c| ≤ c / 2 := by
    have e : t - (j0 : ℝ) * c = c * (t / c - j0) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hc0]
    have hq1 : -(1 / 2 : ℝ) ≤ t / c - j0 := by linarith
    have hq2 : t / c - j0 ≤ 1 / 2 := by linarith
    have hq : |t / c - j0| ≤ 1 / 2 := abs_le.mpr ⟨hq1, hq2⟩
    nlinarith [abs_nonneg (t / c - j0)]
  -- pointwise bound for the shifted index
  have key : ∀ k : ℤ, Real.exp (-((t - ((k + j0 : ℤ) : ℝ) * c) ^ 2) / (8 * a))
      ≤ Real.exp (-α * (k : ℝ) ^ 2) := by
    intro k
    obtain ⟨w, hw⟩ : ∃ w : ℝ, w = t - ((k + j0 : ℤ) : ℝ) * c := ⟨_, rfl⟩
    rw [← hw]
    have hwu : w = (t - (j0 : ℝ) * c) - (k : ℝ) * c := by
      rw [hw]; push_cast; ring
    -- |w| ≥ |k| / 2
    have hwk : |(k : ℝ)| / 2 ≤ |w| := by
      rcases eq_or_ne k 0 with hk | hk
      · simp [hk]
      · have hK1 : (1 : ℝ) ≤ |(k : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast Int.one_le_abs hk
        have hkc : |(k : ℝ) * c| = |(k : ℝ)| * c := by
          rw [abs_mul, abs_of_pos hc0]
        have htri : |(k : ℝ) * c| ≤ |t - (j0 : ℝ) * c| + |w| := by
          have e2 : (k : ℝ) * c = (t - (j0 : ℝ) * c) - w := by rw [hwu]; ring
          rw [e2]
          exact abs_sub _ _
        have hK : |(k : ℝ)| * c ≤ c / 2 + |w| := by
          rw [← hkc]; linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hK1) (sub_nonneg.mpr hc)]
    -- squared bound
    have hsq : (k : ℝ) ^ 2 / 4 ≤ w ^ 2 := by
      have h0 : 0 ≤ |(k : ℝ)| / 2 := by positivity
      have h3 := pow_le_pow_left₀ h0 hwk 2
      rw [sq_abs] at h3
      have e3 : (|(k : ℝ)| / 2) ^ 2 = (k : ℝ) ^ 2 / 4 := by
        rw [div_pow, sq_abs]; norm_num
      rw [e3] at h3
      exact h3
    have hk0 : 0 ≤ α * (k : ℝ) ^ 2 := by positivity
    have hexp : α * (k : ℝ) ^ 2 ≤ w ^ 2 / (8 * a) := by
      rw [le_div_iff₀ (by positivity)]
      have h8 : 8 * a ≤ 8 * (21 / 10) := by linarith
      have hk4 : α * (k : ℝ) ^ 2 * (8 * (21 / 10)) = (k : ℝ) ^ 2 / 4 := by
        rw [show α * (k : ℝ) ^ 2 * (8 * (21 / 10)) = (α * (8 * (21 / 10))) * (k : ℝ) ^ 2 by ring,
          hαv]
        ring
      have hh := mul_le_mul_of_nonneg_left h8 hk0
      linarith
    rw [neg_div, neg_mul]
    apply Real.exp_le_exp.mpr
    exact neg_le_neg hexp
  have hsumm : Summable (fun k : ℤ => Real.exp (-((t - ((k + j0 : ℤ) : ℝ) * c) ^ 2) / (8 * a))) :=
    Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) key hS
  calc ∑' j : ℤ, Real.exp (-((t - (j : ℝ) * c) ^ 2) / (8 * a))
      = ∑' k : ℤ, Real.exp (-((t - ((k + j0 : ℤ) : ℝ) * c) ^ 2) / (8 * a)) :=
        ((Equiv.addRight j0).tsum_eq
          (fun j : ℤ => Real.exp (-((t - (j : ℝ) * c) ^ 2) / (8 * a)))).symm
    _ ≤ ∑' k : ℤ, Real.exp (-α * (k : ℝ) ^ 2) := Summable.tsum_le_tsum key hsumm hS

end UnforcedLeray.Short.PartIIIb.Concrete
