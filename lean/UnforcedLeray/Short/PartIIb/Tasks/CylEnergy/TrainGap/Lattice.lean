import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TrainGap.Iso

/-!
# Train gap, helper: lattice sums of the Gaussian decay

For `β > 0` and `c ≥ 1`, with `γ = β/4`:

* `lattice_uniform`: `∑_n e^{-β(x - n c)²} ≤ ∑_m e^{-γ m²}` for every `x` (uniform in `x`),
* `tail_exp_le`: for `|x| ≤ c/2` and `n ≠ 0`, `e^{-β(x - n c)²} ≤ e^{γ} e^{-γ c²} e^{-γ n²}`,
* `tsum_ite_zero_bound`: the sum over `n ≠ 0` of a summand dominated by a summable `H` is bounded
  by `∑ H` (this is the image part of the train comparison on the cell),
* `abs_tsum_le'`: the absolute value of a series is bounded by the majorant series.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.TrainGap

/-- `|∑ f| ≤ ∑ g` whenever `|f n| ≤ g n` and `g` is summable. -/
theorem abs_tsum_le' {f g : ℤ → ℝ} (hg : Summable g) (h : ∀ n, |f n| ≤ g n) :
    |∑' n, f n| ≤ ∑' n, g n := by
  have hnorm : ∀ n, ‖f n‖ ≤ g n := fun n => by rw [Real.norm_eq_abs]; exact h n
  have hsum : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnorm hg
  calc |∑' n, f n| = ‖∑' n, f n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n, g n := Summable.tsum_le_tsum hnorm hsum hg

/-- The series with the `n = 0` term removed is bounded by the majorant series. -/
theorem tsum_ite_zero_bound {f H : ℤ → ℝ} (hf : Summable f) (hH : Summable H)
    (hH0 : ∀ n, 0 ≤ H n) (hb : ∀ n, n ≠ 0 → |f n| ≤ H n) :
    |∑' n, f n - f 0| ≤ ∑' n, H n := by
  classical
  have hsplit : ∑' n, f n = f 0 + ∑' n, (if n = 0 then (0 : ℝ) else f n) :=
    hf.tsum_eq_add_tsum_ite 0
  have hbound : ∀ n, ‖(if n = 0 then (0 : ℝ) else f n)‖ ≤ H n := by
    intro n
    by_cases hn : n = 0
    · rw [if_pos hn, norm_zero]
      exact hH0 n
    · rw [if_neg hn, Real.norm_eq_abs]
      exact hb n hn
  have hsum : Summable (fun n => ‖(if n = 0 then (0 : ℝ) else f n)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hH
  have h1 : ‖∑' n, (if n = 0 then (0 : ℝ) else f n)‖ ≤
      ∑' n, ‖(if n = 0 then (0 : ℝ) else f n)‖ := norm_tsum_le_tsum_norm hsum
  have h2 : ∑' n, ‖(if n = 0 then (0 : ℝ) else f n)‖ ≤ ∑' n, H n :=
    Summable.tsum_le_tsum hbound hsum hH
  have e : ∑' n, f n - f 0 = ∑' n, (if n = 0 then (0 : ℝ) else f n) := by
    rw [hsplit]
    ring
  rw [e, ← Real.norm_eq_abs]
  exact h1.trans h2

/-- Summability of a series dominated by a Gaussian lattice translate `e^{-β(x - n c)²}`. -/
theorem summable_of_gauss_bound {g : ℤ → ℝ} {A β c x : ℝ} (hβ : 0 < β) (hc : c ≠ 0)
    (h : ∀ n : ℤ, |g n| ≤ A * Real.exp (-(β * (x - n * c) ^ 2))) : Summable g := by
  refine Summable.of_norm_bounded ((UnforcedLeray.B0146.summable_exp_shift hβ hc x).mul_left A) ?_
  intro n
  rw [Real.norm_eq_abs]
  exact h n

/-- **Uniform lattice bound.** For `β > 0`, `c ≥ 1`, every `x`, the Gaussian lattice sum is
dominated by the lattice sum `∑_m e^{-(β/4) m²}`, which does not depend on `x` or `c`. -/
theorem lattice_uniform {β c : ℝ} (hβ : 0 < β) (hc : 1 ≤ c) (x : ℝ) :
    ∑' n : ℤ, Real.exp (-(β * (x - n * c) ^ 2)) ≤
      ∑' m : ℤ, Real.exp (-((β / 4) * (m : ℝ) ^ 2)) := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  obtain ⟨k, hk⟩ := exists_round hcpos x
  have hγ : 0 < β / 4 := by linarith
  have hsum_f : Summable (fun n : ℤ => Real.exp (-(β * (x - n * c) ^ 2))) :=
    UnforcedLeray.B0146.summable_exp_shift hβ hcpos.ne' x
  have hg : Summable (fun m : ℤ => Real.exp (-((β / 4) * (m : ℝ) ^ 2))) :=
    summable_gauss_int hγ
  have hg' : Summable (fun n : ℤ => Real.exp (-((β / 4) * ((n - k : ℤ) : ℝ) ^ 2))) :=
    (Equiv.subRight k).summable_iff.mpr hg
  have hpt : ∀ n : ℤ, Real.exp (-(β * (x - n * c) ^ 2)) ≤
      Real.exp (-((β / 4) * ((n - k : ℤ) : ℝ) ^ 2)) := by
    intro n
    have hsep := lattice_sep hc hk n
    have h0 : 0 ≤ |((n - k : ℤ) : ℝ)| * c / 2 :=
      div_nonneg (mul_nonneg (abs_nonneg _) hcpos.le) (by norm_num)
    have hsq : (|((n - k : ℤ) : ℝ)| * c / 2) ^ 2 ≤ |x - n * c| ^ 2 :=
      pow_le_pow_left₀ h0 hsep 2
    rw [sq_abs] at hsq
    have e1 : (|((n - k : ℤ) : ℝ)| * c / 2) ^ 2 = ((n - k : ℤ) : ℝ) ^ 2 * c ^ 2 / 4 := by
      rw [div_pow, mul_pow, sq_abs]
      ring
    rw [e1] at hsq
    have hc2 : 1 ≤ c ^ 2 := by nlinarith
    have hm2 : 0 ≤ ((n - k : ℤ) : ℝ) ^ 2 := sq_nonneg _
    have key : ((n - k : ℤ) : ℝ) ^ 2 / 4 ≤ (x - n * c) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hc2 hm2]
    have hmul := mul_le_mul_of_nonneg_left key hβ.le
    apply Real.exp_le_exp.mpr
    nlinarith [hmul]
  calc ∑' n : ℤ, Real.exp (-(β * (x - n * c) ^ 2))
      ≤ ∑' n : ℤ, Real.exp (-((β / 4) * ((n - k : ℤ) : ℝ) ^ 2)) :=
        Summable.tsum_le_tsum hpt hsum_f hg'
    _ = ∑' m : ℤ, Real.exp (-((β / 4) * (m : ℝ) ^ 2)) :=
        (Equiv.subRight k).tsum_eq (fun m : ℤ => Real.exp (-((β / 4) * (m : ℝ) ^ 2)))

/-- **Tail bound on the cell.** For `c ≥ 1`, `|x| ≤ c/2` and `n ≠ 0`:
`e^{-β(x - n c)²} ≤ e^{β/4} e^{-(β/4) c²} e^{-(β/4) n²}`. -/
theorem tail_exp_le {β c x : ℝ} (hβ : 0 < β) (hc : 1 ≤ c) (hx : |x| ≤ c / 2) {n : ℤ}
    (hn : n ≠ 0) :
    Real.exp (-(β * (x - n * c) ^ 2)) ≤
      Real.exp (β / 4) * Real.exp (-((β / 4) * c ^ 2)) * Real.exp (-((β / 4) * (n : ℝ) ^ 2)) := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have hγ : 0 < β / 4 := by linarith
  have hk : |x - ((0 : ℤ) : ℝ) * c| ≤ c / 2 := by simpa using hx
  have hsep := lattice_sep hc hk n
  simp only [sub_zero] at hsep
  have h0 : 0 ≤ |(n : ℝ)| * c / 2 :=
    div_nonneg (mul_nonneg (abs_nonneg _) hcpos.le) (by norm_num)
  have hsq : (|(n : ℝ)| * c / 2) ^ 2 ≤ |x - n * c| ^ 2 := pow_le_pow_left₀ h0 hsep 2
  rw [sq_abs] at hsq
  have e1 : (|(n : ℝ)| * c / 2) ^ 2 = (n : ℝ) ^ 2 * c ^ 2 / 4 := by
    rw [div_pow, mul_pow, sq_abs]
    ring
  rw [e1] at hsq
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.mpr h1
    rw [Int.cast_abs] at h2
    simpa using h2
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [← sq_abs]
    nlinarith
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  have hprod : 0 ≤ ((n : ℝ) ^ 2 - 1) * (c ^ 2 - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hexp : -((β / 4) * ((n : ℝ) ^ 2 * c ^ 2)) ≤
      β / 4 + -((β / 4) * c ^ 2) + -((β / 4) * (n : ℝ) ^ 2) := by
    nlinarith [mul_nonneg hγ.le hprod]
  have hsec : -(β * (x - n * c) ^ 2) ≤ -((β / 4) * ((n : ℝ) ^ 2 * c ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hsq hβ.le
    nlinarith [this]
  calc Real.exp (-(β * (x - n * c) ^ 2))
      ≤ Real.exp (β / 4 + -((β / 4) * c ^ 2) + -((β / 4) * (n : ℝ) ^ 2)) :=
        Real.exp_le_exp.mpr (le_trans hsec hexp)
    _ = Real.exp (β / 4) * Real.exp (-((β / 4) * c ^ 2)) * Real.exp (-((β / 4) * (n : ℝ) ^ 2)) := by
        rw [Real.exp_add, Real.exp_add]

end UnforcedLeray.Short.IIb.TrainGap
