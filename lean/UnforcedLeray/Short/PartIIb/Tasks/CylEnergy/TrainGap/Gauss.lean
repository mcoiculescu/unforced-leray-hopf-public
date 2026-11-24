import UnforcedLeray.Units.B0146.LatticeSums

/-!
# Train gap, helper: elementary Gaussian and lattice bounds

Pure real-analysis facts used by the train-gap estimate `CylTrainGap` (`PartII-b:T22`, leaf 6;
source `the November 2 reference manuscript` lines 2085-2093).

* `t_mul_exp_le`: `t e^{-αt²} ≤ 1/(4α) + 1` for `t ≥ 0`, `α > 0`.
* `exists_round`: every real is within `c/2` of an integer multiple of `c > 0`.
* `lattice_sep`: for `c ≥ 1`, `|x - n c| ≥ |n - k| c / 2` whenever `|x - k c| ≤ c/2`.
* `summable_gauss_int`: `∑_{m ∈ ℤ} e^{-γ m²}` converges for `γ > 0`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.TrainGap

/-- `t e^{-α t²} ≤ 1/(4α) + 1` for `t ≥ 0` and `α > 0`. -/
theorem t_mul_exp_le {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) :
    t * Real.exp (-(α * t ^ 2)) ≤ 1 / (4 * α) + 1 := by
  have hα0 : α ≠ 0 := hα.ne'
  have h1 : t ≤ 1 / (4 * α) + α * t ^ 2 := by
    have key : 1 / (4 * α) + α * t ^ 2 - t = (1 - 2 * α * t) ^ 2 / (4 * α) := by
      field_simp
      ring
    have : 0 ≤ (1 - 2 * α * t) ^ 2 / (4 * α) := div_nonneg (sq_nonneg _) (by positivity)
    linarith
  have hv : 0 ≤ α * t ^ 2 := by positivity
  have hexp1 : Real.exp (-(α * t ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexp0 : 0 < Real.exp (-(α * t ^ 2)) := Real.exp_pos _
  have h2 : (α * t ^ 2) * Real.exp (-(α * t ^ 2)) ≤ 1 := by
    have h3 : α * t ^ 2 ≤ Real.exp (α * t ^ 2) := by
      linarith [Real.add_one_le_exp (α * t ^ 2)]
    have h4 : Real.exp (α * t ^ 2) * Real.exp (-(α * t ^ 2)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc (α * t ^ 2) * Real.exp (-(α * t ^ 2))
        ≤ Real.exp (α * t ^ 2) * Real.exp (-(α * t ^ 2)) :=
          mul_le_mul_of_nonneg_right h3 hexp0.le
      _ = 1 := h4
  have hp : 0 ≤ 1 / (4 * α) := by positivity
  calc t * Real.exp (-(α * t ^ 2))
      ≤ (1 / (4 * α) + α * t ^ 2) * Real.exp (-(α * t ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 hexp0.le
    _ = 1 / (4 * α) * Real.exp (-(α * t ^ 2)) + (α * t ^ 2) * Real.exp (-(α * t ^ 2)) := by
        ring
    _ ≤ 1 / (4 * α) * 1 + 1 := by
        linarith [mul_le_mul_of_nonneg_left hexp1 hp, h2]
    _ = 1 / (4 * α) + 1 := by ring

/-- Every real lies within `c/2` of an integer multiple of `c > 0`. -/
theorem exists_round {c : ℝ} (hc : 0 < c) (x : ℝ) : ∃ k : ℤ, |x - k * c| ≤ c / 2 := by
  refine ⟨⌊x / c + 1 / 2⌋, ?_⟩
  have h1 : ((⌊x / c + 1 / 2⌋ : ℤ) : ℝ) ≤ x / c + 1 / 2 := Int.floor_le _
  have h2 : x / c + 1 / 2 < ((⌊x / c + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : x - ((⌊x / c + 1 / 2⌋ : ℤ) : ℝ) * c
      = (x / c - ((⌊x / c + 1 / 2⌋ : ℤ) : ℝ)) * c := by
    have hc0 : c ≠ 0 := hc.ne'
    field_simp
  have h4 : |x / c - ((⌊x / c + 1 / 2⌋ : ℤ) : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  rw [h3, abs_mul, abs_of_pos hc]
  calc |x / c - ((⌊x / c + 1 / 2⌋ : ℤ) : ℝ)| * c ≤ (1 / 2) * c :=
        mul_le_mul_of_nonneg_right h4 hc.le
    _ = c / 2 := by ring

/-- Lattice separation: if `|x - k c| ≤ c/2` and `c ≥ 1`, then `|n - k| c/2 ≤ |x - n c|`. -/
theorem lattice_sep {c : ℝ} (hc : 1 ≤ c) {x : ℝ} {k : ℤ} (hk : |x - k * c| ≤ c / 2) (n : ℤ) :
    |((n - k : ℤ) : ℝ)| * c / 2 ≤ |x - n * c| := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have hx : x - n * c = (x - k * c) - ((n - k : ℤ) : ℝ) * c := by
    push_cast
    ring
  rcases eq_or_ne (n - k : ℤ) 0 with h0 | h0
  · rw [h0]
    simp only [Int.cast_zero, abs_zero, zero_mul, zero_div]
    exact abs_nonneg _
  · have hm1 : (1 : ℝ) ≤ |((n - k : ℤ) : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |n - k| := Int.one_le_abs h0
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|n - k| : ℤ) : ℝ) := Int.cast_le.mpr h1
      rw [Int.cast_abs] at h2
      simpa using h2
    have htri : |((n - k : ℤ) : ℝ) * c| - |x - k * c| ≤ |(x - k * c) - ((n - k : ℤ) : ℝ) * c| := by
      have h5 := abs_sub_abs_le_abs_sub (((n - k : ℤ) : ℝ) * c) (x - k * c)
      rw [abs_sub_comm (((n - k : ℤ) : ℝ) * c) (x - k * c)] at h5
      exact h5
    rw [abs_mul, abs_of_pos hcpos] at htri
    rw [hx]
    nlinarith [mul_nonneg hcpos.le (sub_nonneg.mpr hm1)]

/-- The Gaussian lattice sum `∑_{m ∈ ℤ} e^{-γ m²}` converges for `γ > 0`. -/
theorem summable_gauss_int {γ : ℝ} (hγ : 0 < γ) :
    Summable (fun m : ℤ => Real.exp (-(γ * (m : ℝ) ^ 2))) := by
  have h := UnforcedLeray.B0146.summable_exp_shift hγ one_ne_zero (0 : ℝ)
  refine h.congr ?_
  intro n
  congr 1
  ring

end UnforcedLeray.Short.IIb.TrainGap
