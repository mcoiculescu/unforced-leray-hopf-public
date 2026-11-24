import UnforcedLeray.Short.PartI.Sub.T02_4

/-!
# Part I, task `PartI:T02/4` (`TrainDatumCurlSech`): the datum vorticity has sech tails

Source of record: `the November 2 reference manuscript`, lines 262-270 (the train
datum has vorticity in `L¹ ∩ L^∞`; the datum vorticity is the periodized Gaussian
`(2 - |x|²/2) e^{-|x|²/4}`).

Target: `TrainDatumCurlSech` (`Short/PartI/Sub/T02_4.lean`): for every `c ≥ 1` there are `A, a > 0`
with `|curl (trainDatum c) z| ≤ A / cosh (a η)`.  We prove it with `a = 1`.

Route:
* `curl (trainDatum c) = P_c ω₀` (`B0140.curl_trainDatum`), so
  `|curl (trainDatum c) (q, η)| ≤ 4 e^{-η²/8} ∑_n e^{-(q - nc)²/8}` (`tdVortAbsLe`).
* For `c ≥ 1` the lattice sum is bounded uniformly in `q`: with the nearest index
  `n₀ = round (q/c)` one has `|q - nc| ≥ |n - n₀| / 2`, so the sum is at most
  `∑_m e^{-m²/32}` (`tdLatticeBound`).
* `e^{-η²/8} cosh η ≤ e^{|η| - η²/8} ≤ e²`, because `|η| - η²/8 = 2 - (|η| - 4)²/8 ≤ 2`.

The library bound `Gaussian.norm_periodize_le_of_gauss` needs `2 ≤ c²`, so it does not cover
`1 ≤ c < √2`; the lattice sum is therefore estimated directly here.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- A radial bound: `|(2 - r/2) e^{-r/4}| ≤ 4 e^{-r/8}` for `r ≥ 0`. -/
theorem tdRadial (r : ℝ) (hr : 0 ≤ r) :
    |(2 - r / 2) * Real.exp (-(r / 4))| ≤ 4 * Real.exp (-r / (4 * 2)) := by
  have hE : 0 < Real.exp (-r / (4 * 2)) := Real.exp_pos _
  have hsplit : Real.exp (-(r / 4)) = Real.exp (-r / (4 * 2)) * Real.exp (-r / (4 * 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h8 : 1 + r / 8 ≤ Real.exp (r / 8) := by
    have := Real.add_one_le_exp (r / 8); linarith
  have hinv : Real.exp (r / 8) * Real.exp (-r / (4 * 2)) = 1 := by
    rw [mul_comm (Real.exp (r / 8)), ← Real.exp_add]
    have h0 : -r / (4 * 2) + r / 8 = 0 := by ring
    rw [h0, Real.exp_zero]
  have hkey : (1 + r / 8) * Real.exp (-r / (4 * 2)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h8 hE.le
    linarith
  have habs : |2 - r / 2| ≤ 4 * (1 + r / 8) := by
    rw [abs_le]; constructor <;> linarith
  rw [hsplit, abs_mul, abs_of_pos (mul_pos hE hE)]
  have hA : |2 - r / 2| * Real.exp (-r / (4 * 2)) ≤ 4 := by
    calc |2 - r / 2| * Real.exp (-r / (4 * 2))
        ≤ (4 * (1 + r / 8)) * Real.exp (-r / (4 * 2)) :=
          mul_le_mul_of_nonneg_right habs hE.le
      _ = 4 * ((1 + r / 8) * Real.exp (-r / (4 * 2))) := by ring
      _ ≤ 4 * 1 := mul_le_mul_of_nonneg_left hkey (by norm_num)
      _ = 4 := by norm_num
  calc |2 - r / 2| * (Real.exp (-r / (4 * 2)) * Real.exp (-r / (4 * 2)))
      = (|2 - r / 2| * Real.exp (-r / (4 * 2))) * Real.exp (-r / (4 * 2)) := by ring
    _ ≤ 4 * Real.exp (-r / (4 * 2)) := mul_le_mul_of_nonneg_right hA hE.le

/-- The Gaussian stream vorticity: `|ω(x, η)| ≤ 4 e^{-(x²+η²)/8}`. -/
theorem tdVortAbsLe (x η : ℝ) :
    |GaussianVortex.vorticity (x, η)| ≤ 4 * Real.exp (-(x ^ 2 + η ^ 2) / (4 * 2)) := by
  show |(2 - (x ^ 2 + η ^ 2) / 2) * Real.exp (-((x ^ 2 + η ^ 2) / 4))| ≤ _
  exact tdRadial _ (by positivity)

/-- `m ↦ e^{-m²/32}` is summable over `ℤ` (dominated by a geometric series on each half-line). -/
theorem tdGaussIntSummable : Summable (fun m : ℤ => Real.exp (-((m : ℝ) ^ 2) / 32)) := by
  have hg : Summable (fun m : ℕ => Real.exp (-(1 / 32 : ℝ) * (m : ℝ))) :=
    UnforcedLeray.Gaussian.summable_exp_neg_mul_nat (by norm_num)
  refine (UnforcedLeray.Gaussian.tsum_int_le_of_le_two_sides
    (f := fun m : ℤ => Real.exp (-((m : ℝ) ^ 2) / 32))
    (g := fun m : ℕ => Real.exp (-(1 / 32 : ℝ) * (m : ℝ)))
    (fun n => (Real.exp_pos _).le) hg ?_ ?_).1
  · intro m
    have hcm : ((m : ℤ) : ℝ) = (m : ℝ) := by norm_cast
    rw [hcm]
    apply Real.exp_le_exp.2
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hm2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp
      · have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
        nlinarith
    linarith
  · intro m
    have hcast : ((-((m : ℤ) + 1) : ℤ) : ℝ) = -((m : ℝ) + 1) := by simp
    rw [hcast]
    apply Real.exp_le_exp.2
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [sq_nonneg (m : ℝ)]

/-- Uniform lattice bound: for `c ≥ 1` and every `q`, the lattice sum `∑_n e^{-(q - nc)²/8}` is
summable and at most `∑_m e^{-m²/32}`. -/
theorem tdLatticeBound {c : ℝ} (hc : 1 ≤ c) (q : ℝ) :
    Summable (fun n : ℤ => Real.exp (-(q - (n : ℝ) * c) ^ 2 / 8)) ∧
      ∑' n : ℤ, Real.exp (-(q - (n : ℝ) * c) ^ 2 / 8) ≤
        ∑' m : ℤ, Real.exp (-((m : ℝ) ^ 2) / 32) := by
  have hcpos : 0 < c := by linarith
  have hc0 : c ≠ 0 := hcpos.ne'
  obtain ⟨n0, hround⟩ : ∃ n0 : ℤ, |q / c - (n0 : ℝ)| ≤ 1 / 2 :=
    ⟨round (q / c), abs_sub_round (q / c)⟩
  have hcq : c * (q / c) = q := by field_simp
  have hb : |q - (n0 : ℝ) * c| ≤ c / 2 := by
    have e : q - (n0 : ℝ) * c = c * (q / c - (n0 : ℝ)) := by
      linear_combination (-1 : ℝ) * hcq
    rw [e, abs_mul, abs_of_pos hcpos]
    have := mul_le_mul_of_nonneg_left hround hcpos.le
    linarith
  have hkey : ∀ n : ℤ, |((n - n0 : ℤ) : ℝ)| / 2 ≤ |q - (n : ℝ) * c| := by
    intro n
    have htri : |((n - n0 : ℤ) : ℝ) * c| - |q - (n0 : ℝ) * c| ≤ |q - (n : ℝ) * c| := by
      have h1 := abs_sub_abs_le_abs_sub (((n - n0 : ℤ) : ℝ) * c) (q - (n0 : ℝ) * c)
      have h2 : ((n - n0 : ℤ) : ℝ) * c - (q - (n0 : ℝ) * c) = -(q - (n : ℝ) * c) := by
        push_cast; ring
      rw [h2, abs_neg] at h1
      exact h1
    rw [abs_mul, abs_of_pos hcpos] at htri
    by_cases hm0 : n - n0 = 0
    · have h0 : ((n - n0 : ℤ) : ℝ) = 0 := by rw [hm0]; simp
      rw [h0]; simp
    · have h1 : (1 : ℝ) ≤ |((n - n0 : ℤ) : ℝ)| := by
        have : (1 : ℤ) ≤ |n - n0| := Int.one_le_abs hm0
        exact_mod_cast this
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (show (0 : ℝ) ≤ c - 1 / 2 by linarith)]
  have hterm : ∀ n : ℤ, Real.exp (-(q - (n : ℝ) * c) ^ 2 / 8) ≤
      Real.exp (-(((n - n0 : ℤ) : ℝ) ^ 2) / 32) := by
    intro n
    apply Real.exp_le_exp.2
    have h1 := hkey n
    have h0 : 0 ≤ |((n - n0 : ℤ) : ℝ)| / 2 := by positivity
    have hmul := mul_le_mul h1 h1 h0 (abs_nonneg _)
    have h2 : ((n - n0 : ℤ) : ℝ) ^ 2 / 4 ≤ (q - (n : ℝ) * c) ^ 2 := by
      nlinarith [sq_abs ((n - n0 : ℤ) : ℝ), sq_abs (q - (n : ℝ) * c)]
    linarith
  have hSn : Summable (fun n : ℤ => Real.exp (-(((n - n0 : ℤ) : ℝ) ^ 2) / 32)) :=
    (Equiv.summable_iff (Equiv.subRight n0)).2 tdGaussIntSummable
  have hG : Summable (fun n : ℤ => Real.exp (-(q - (n : ℝ) * c) ^ 2 / 8)) :=
    Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hterm hSn
  refine ⟨hG, ?_⟩
  calc ∑' n : ℤ, Real.exp (-(q - (n : ℝ) * c) ^ 2 / 8)
      ≤ ∑' n : ℤ, Real.exp (-(((n - n0 : ℤ) : ℝ) ^ 2) / 32) := hG.tsum_le_tsum hterm hSn
    _ = ∑' m : ℤ, Real.exp (-((m : ℝ) ^ 2) / 32) :=
        (Equiv.subRight n0).tsum_eq (fun m : ℤ => Real.exp (-((m : ℝ) ^ 2) / 32))

/-- **The datum vorticity has sech tails** (`TrainDatumCurlSech`, source lines 262-270): for
`c ≥ 1`, `|curl (trainDatum c) z| ≤ A / cosh (a η)` with `a = 1`. -/
theorem trainDatumCurlSech : TrainDatumCurlSech := by
  unfold TrainDatumCurlSech
  intro c hc
  have hcpos : 0 < c := by linarith
  have hc0 : c ≠ 0 := hcpos.ne'
  have hK0 : 0 ≤ ∑' m : ℤ, Real.exp (-((m : ℝ) ^ 2) / 32) :=
    tsum_nonneg (fun m => (Real.exp_pos _).le)
  refine ⟨4 * ((∑' m : ℤ, Real.exp (-((m : ℝ) ^ 2) / 32)) + 1) * Real.exp 2, 1,
    mul_pos (mul_pos (by norm_num) (by linarith)) (Real.exp_pos 2), one_pos, ?_⟩
  intro z
  rw [one_mul]
  -- the sech factor: e^{-η²/8} ≤ e² (cosh η)⁻¹
  have hAbound : Real.exp (-(z.2 ^ 2) / 8) ≤ Real.exp 2 * (Real.cosh z.2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (Real.cosh_pos _)]
    have hcosh : Real.cosh z.2 ≤ Real.exp |z.2| := by
      rw [Real.cosh_eq]
      have h1 := Real.exp_le_exp_of_le (le_abs_self z.2)
      have h2 := Real.exp_le_exp_of_le (neg_le_abs z.2)
      linarith
    have hprod : Real.exp (-(z.2 ^ 2) / 8) * Real.cosh z.2 ≤
        Real.exp (-(z.2 ^ 2) / 8) * Real.exp |z.2| :=
      mul_le_mul_of_nonneg_left hcosh (Real.exp_pos _).le
    have hexp : Real.exp (-(z.2 ^ 2) / 8) * Real.exp |z.2| =
        Real.exp (|z.2| + -(z.2 ^ 2) / 8) := by
      rw [← Real.exp_add]; congr 1; ring
    have hle : |z.2| + -(z.2 ^ 2) / 8 ≤ 2 := by
      nlinarith [sq_abs z.2, sq_nonneg (|z.2| - 4)]
    have hE : Real.exp (|z.2| + -(z.2 ^ 2) / 8) ≤ Real.exp 2 := Real.exp_le_exp.2 hle
    linarith
  -- the pointwise vorticity bound and its lattice sum
  rw [B0140.curl_trainDatum hc0 z]
  show |∑' n : ℤ, GaussianVortex.vorticity (z.1 - (n : ℝ) * c, z.2)| ≤ _
  have hbound : ∀ n : ℤ, ‖GaussianVortex.vorticity (z.1 - (n : ℝ) * c, z.2)‖ ≤
      4 * (Real.exp (-(z.2 ^ 2) / 8) * Real.exp (-(z.1 - (n : ℝ) * c) ^ 2 / 8)) := by
    intro n
    have h := tdVortAbsLe (z.1 - (n : ℝ) * c) z.2
    have e : Real.exp (-((z.1 - (n : ℝ) * c) ^ 2 + z.2 ^ 2) / (4 * 2)) =
        Real.exp (-(z.2 ^ 2) / 8) * Real.exp (-(z.1 - (n : ℝ) * c) ^ 2 / 8) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e] at h
    rw [Real.norm_eq_abs]
    exact h
  obtain ⟨hGs, hGle⟩ := tdLatticeBound hc z.1
  have hFs : Summable (fun n : ℤ =>
      4 * (Real.exp (-(z.2 ^ 2) / 8) * Real.exp (-(z.1 - (n : ℝ) * c) ^ 2 / 8))) :=
    (hGs.mul_left (Real.exp (-(z.2 ^ 2) / 8))).mul_left 4
  have hnorm : Summable (fun n : ℤ => ‖GaussianVortex.vorticity (z.1 - (n : ℝ) * c, z.2)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hFs
  have hA0 : 0 ≤ Real.exp (-(z.2 ^ 2) / 8) := (Real.exp_pos _).le
  have hS0 : 0 ≤ Real.exp 2 * (Real.cosh z.2)⁻¹ :=
    mul_nonneg (Real.exp_pos _).le (inv_nonneg.2 (Real.cosh_pos _).le)
  have hfin1 : Real.exp (-(z.2 ^ 2) / 8) * (∑' m : ℤ, Real.exp (-((m : ℝ) ^ 2) / 32))
      ≤ (Real.exp 2 * (Real.cosh z.2)⁻¹) * (∑' m : ℤ, Real.exp (-((m : ℝ) ^ 2) / 32)) :=
    mul_le_mul_of_nonneg_right hAbound hK0
  calc |∑' n : ℤ, GaussianVortex.vorticity (z.1 - (n : ℝ) * c, z.2)|
      = ‖∑' n : ℤ, GaussianVortex.vorticity (z.1 - (n : ℝ) * c, z.2)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℤ, ‖GaussianVortex.vorticity (z.1 - (n : ℝ) * c, z.2)‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℤ, 4 * (Real.exp (-(z.2 ^ 2) / 8) * Real.exp (-(z.1 - (n : ℝ) * c) ^ 2 / 8)) :=
        hnorm.tsum_le_tsum hbound hFs
    _ = 4 * (Real.exp (-(z.2 ^ 2) / 8) * ∑' n : ℤ, Real.exp (-(z.1 - (n : ℝ) * c) ^ 2 / 8)) := by
        rw [tsum_mul_left, tsum_mul_left]
    _ ≤ 4 * (Real.exp (-(z.2 ^ 2) / 8) * (∑' m : ℤ, Real.exp (-((m : ℝ) ^ 2) / 32))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGle hA0) (by norm_num)
    _ ≤ 4 * ((∑' m : ℤ, Real.exp (-((m : ℝ) ^ 2) / 32)) + 1) * Real.exp 2 * (Real.cosh z.2)⁻¹ := by
        nlinarith [hfin1, hS0]

end UnforcedLeray.Short.PartI
