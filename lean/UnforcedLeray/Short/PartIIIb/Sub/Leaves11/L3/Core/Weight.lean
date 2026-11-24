import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11_3_3

/-!
# `PartIII-b:C/inst/11/3/3/2`: uniform Gaussian weight sum over a lattice of spacing `c ≥ 1`

Source `shorter-proof-2026-11-02.tex` lines 5063-5079 (Gaussian weights in the Cauchy-Schwarz step).
Let `m = ⌊t/c + 1/2⌋`. Then `t - m c ∈ [-c/2, c/2)`, and for `k = n - m` one has
`|t - n c| ≥ |k|/2` (for `k ≠ 0`, using `c ≥ 1`). With `a ≤ 21/10` the Gaussian term is at most
`exp(-(5/336)|k|)`, a summable majorant independent of `c`, `a`, `t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Pointwise bound on one term of the lattice weight sum, in terms of the integer offset `n - m`. -/
theorem latWeight_pt (c a t : ℝ) (hc : 1 ≤ c) (ha1 : 1 ≤ a) (ha2 : a ≤ 21 / 10)
    (m n : ℤ) (hfl1 : (m : ℝ) ≤ t / c + 1 / 2) (hfl2 : t / c + 1 / 2 < (m : ℝ) + 1) :
    Real.exp (-(t - (n : ℝ) * c) ^ 2 / (8 * a)) ≤
      Real.exp (-((5 / 336) * |((n - m : ℤ) : ℝ)|)) := by
  have hc0 : 0 < c := by linarith
  have hA : (m : ℝ) - 1 / 2 ≤ t / c := by linarith
  have hA' : ((m : ℝ) - 1 / 2) * c ≤ t := (le_div_iff₀ hc0).1 hA
  have hB : t / c < (m : ℝ) + 1 / 2 := by linarith
  have hB' : t < ((m : ℝ) + 1 / 2) * c := (div_lt_iff₀ hc0).1 hB
  have e1 : ((m : ℝ) - 1 / 2) * c = (m : ℝ) * c - c / 2 := by ring
  have e2 : ((m : ℝ) + 1 / 2) * c = (m : ℝ) * c + c / 2 := by ring
  have hr1 : -(c / 2) ≤ t - (m : ℝ) * c := by linarith
  have hr2 : t - (m : ℝ) * c < c / 2 := by linarith
  -- the offset k = n - m and the identity t - n c = (t - m c) - k c
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ((n - m : ℤ) : ℝ) := ⟨_, rfl⟩
  have hu : t - (n : ℝ) * c = (t - (m : ℝ) * c) - K * c := by
    rw [hK]; push_cast; ring
  -- integer fact |K| ≤ K^2
  have hI : |K| ≤ K ^ 2 := by
    rcases lt_trichotomy (n - m) 0 with h | h | h
    · have hK1 : K ≤ -1 := by rw [hK]; exact_mod_cast (show n - m ≤ -1 by omega)
      rw [abs_of_nonpos (by linarith)]
      nlinarith
    · have hK0 : K = 0 := by rw [hK, h]; simp
      rw [hK0]; simp
    · have hK1 : 1 ≤ K := by rw [hK]; exact_mod_cast (show 1 ≤ n - m by omega)
      rw [abs_of_nonneg (by linarith)]
      nlinarith
  -- lower bound for the squared distance: |K|/4 ≤ u^2
  have hmain : |K| / 4 ≤ (t - (n : ℝ) * c) ^ 2 := by
    rcases lt_trichotomy (n - m) 0 with h | h | h
    · have hK1 : K ≤ -1 := by rw [hK]; exact_mod_cast (show n - m ≤ -1 by omega)
      have hu3 : -K / 2 ≤ t - (n : ℝ) * c := by
        rw [hu]
        nlinarith [mul_nonneg (show (0:ℝ) ≤ -K - 1 by linarith) (show (0:ℝ) ≤ c - 1 by linarith)]
      have hsq : (-K / 2) ^ 2 ≤ (t - (n : ℝ) * c) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hu3 2
      have hsq' : K ^ 2 / 4 ≤ (t - (n : ℝ) * c) ^ 2 := by
        have : (-K / 2) ^ 2 = K ^ 2 / 4 := by ring
        linarith
      linarith
    · have hK0 : K = 0 := by rw [hK, h]; simp
      rw [hK0]
      simp only [abs_zero, zero_div]
      positivity
    · have hK1 : 1 ≤ K := by rw [hK]; exact_mod_cast (show 1 ≤ n - m by omega)
      have hu3 : K / 2 ≤ -(t - (n : ℝ) * c) := by
        rw [hu]
        nlinarith [mul_nonneg (show (0:ℝ) ≤ K - 1 by linarith) (show (0:ℝ) ≤ c - 1 by linarith)]
      have hsq : (K / 2) ^ 2 ≤ (-(t - (n : ℝ) * c)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hu3 2
      have hsq' : K ^ 2 / 4 ≤ (t - (n : ℝ) * c) ^ 2 := by
        have : (K / 2) ^ 2 = K ^ 2 / 4 := by ring
        have h2 : (-(t - (n : ℝ) * c)) ^ 2 = (t - (n : ℝ) * c) ^ 2 := by ring
        linarith
      linarith
  -- the Gaussian exponent
  have hdiv : (5 / 336) * |K| ≤ (t - (n : ℝ) * c) ^ 2 / (8 * a) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 8 * a)]
    have h8 : 8 * a ≤ 168 / 10 := by linarith
    have hpos : (0 : ℝ) ≤ (5 / 336) * |K| := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h8 hpos]
  rw [← hK]
  apply Real.exp_le_exp.2
  rw [neg_div]
  exact neg_le_neg hdiv

/-- Summable majorant of the lattice weights, independent of the spacing and of the shift. -/
theorem latWeight_summable_majorant :
    Summable (fun k : ℤ => Real.exp (-((5 / 336) * |(k : ℝ)|))) := by
  apply Summable.of_nat_of_neg
  · refine (Real.summable_pow_mul_exp_neg_nat_mul 0 (by norm_num : (0 : ℝ) < 5 / 336)).congr
      (fun n => ?_)
    simp
  · refine (Real.summable_pow_mul_exp_neg_nat_mul 0 (by norm_num : (0 : ℝ) < 5 / 336)).congr
      (fun n => ?_)
    simp

theorem latWeight : LatWeight := by
  refine ⟨∑' k : ℤ, Real.exp (-((5 / 336) * |(k : ℝ)|)),
    tsum_nonneg (fun k => (Real.exp_pos _).le), fun c a t hc ha1 ha2 => ?_⟩
  have hgs : Summable (fun n : ℤ => Real.exp (-((5 / 336) * |((n - ⌊t / c + 1 / 2⌋ : ℤ) : ℝ)|))) :=
    (Equiv.summable_iff (Equiv.subRight ⌊t / c + 1 / 2⌋)).2 latWeight_summable_majorant
  have hfl1 : ((⌊t / c + 1 / 2⌋ : ℤ) : ℝ) ≤ t / c + 1 / 2 := Int.floor_le _
  have hfl2 : t / c + 1 / 2 < ((⌊t / c + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hle : ∀ n : ℤ, Real.exp (-(t - (n : ℝ) * c) ^ 2 / (8 * a))
      ≤ Real.exp (-((5 / 336) * |((n - ⌊t / c + 1 / 2⌋ : ℤ) : ℝ)|)) :=
    fun n => latWeight_pt c a t hc ha1 ha2 _ n hfl1 hfl2
  have hsum : Summable (fun n : ℤ => Real.exp (-(t - (n : ℝ) * c) ^ 2 / (8 * a))) :=
    Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hle hgs
  refine ⟨hsum, ?_⟩
  calc ∑' n : ℤ, Real.exp (-(t - (n : ℝ) * c) ^ 2 / (8 * a))
      ≤ ∑' n : ℤ, Real.exp (-((5 / 336) * |((n - ⌊t / c + 1 / 2⌋ : ℤ) : ℝ)|)) :=
        Summable.tsum_le_tsum hle hsum hgs
    _ = ∑' k : ℤ, Real.exp (-((5 / 336) * |(k : ℝ)|)) :=
        Equiv.tsum_eq (Equiv.subRight ⌊t / c + 1 / 2⌋)
          (fun k : ℤ => Real.exp (-((5 / 336) * |(k : ℝ)|)))

end UnforcedLeray.Short.PartIIIb.Concrete
