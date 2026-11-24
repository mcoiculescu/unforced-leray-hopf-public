import UnforcedLeray.Lib.Gaussian.LatticeSum
import UnforcedLeray.Lib.Gaussian.Absorb

/-!
# Exponential tilt of the periodized Gaussian (INF22 G9)


target G9. Unit B0169 (tex 2526–2540, eq. `eq:st18-t00166`): the Gaussian initial vorticity
satisfies `|ω(q,η,0)| ≤ C exp(-λη + C₀λ²)` for every `λ ≥ 0` (and with `η ↦ -η`), uniformly in
the period `c`, "by completing the square in the literal Gaussian; the periodized `q`-sum and
its polynomial prefactor are uniformly bounded".

Main results:
* `exp_neg_sq_div_four_le_tilt`: `e^{-η²/4} ≤ e^{-λη + λ²}` for all real `η, λ` (completing the
  square; `λ` is written `lam`);
* `tsum_periodized_gauss_tilt_le`: `∑_n e^{-((q-nc)² + η²)/4} ≤ 10 e^{-λη+λ²}` for `c² ≥ 1`;
* `tsum_poly_periodized_gauss_tilt_le`: the same with a polynomial prefactor
  `(1 + |q-nc| + |η|)^p`, with a constant depending only on `p`, for `c² ≥ 2`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open Real

/-- **G9 (B0169).** Completing the square: `e^{-η²/4} ≤ e^{-λη+λ²}`. -/
theorem exp_neg_sq_div_four_le_tilt (η lam : ℝ) :
    Real.exp (-η ^ 2 / 4) ≤ Real.exp (-lam * η + lam ^ 2) :=
  Real.exp_le_exp.2 (by nlinarith [sq_nonneg (η / 2 - lam)])

/-- **G9 (B0169, tex 2529–2537).** Uniformly in the period `c` with `c² ≥ 1` and in `q`:
`∑_{n∈ℤ} e^{-((q-nc)² + η²)/4} ≤ 10 e^{-λη+λ²}` for every `λ`. -/
theorem tsum_periodized_gauss_tilt_le {c : ℝ} (hc : 1 ≤ c ^ 2) (q η lam : ℝ) :
    ∑' n : ℤ, Real.exp (-((q - n * c) ^ 2 + η ^ 2) / 4) ≤ 10 * Real.exp (-lam * η + lam ^ 2) := by
  have hsplit : ∀ n : ℤ, Real.exp (-((q - n * c) ^ 2 + η ^ 2) / 4) =
      Real.exp (-(q - n * c) ^ 2 / (4 * 1)) * Real.exp (-η ^ 2 / 4) := by
    intro n; rw [← Real.exp_add]; congr 1; ring
  simp_rw [hsplit]
  rw [tsum_mul_right]
  have h1 := tsum_gauss_shift_le (a := 1) (c := c) one_pos hc q
  have h2 := exp_neg_sq_div_four_le_tilt η lam
  have h0 : 0 ≤ ∑' n : ℤ, Real.exp (-(q - n * c) ^ 2 / (4 * 1)) :=
    tsum_nonneg fun n => (Real.exp_pos _).le
  calc (∑' n : ℤ, Real.exp (-(q - n * c) ^ 2 / (4 * 1))) * Real.exp (-η ^ 2 / 4)
      ≤ 10 * Real.exp (-lam * η + lam ^ 2) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)

/-- `(1+s)^p e^{-s²/8} ≤ C_p` for `s ≥ 0`. -/
theorem one_add_pow_mul_exp_le (p : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℝ, 0 ≤ s → (1 + s) ^ p * Real.exp (-s ^ 2 / 8) ≤ C := by
  obtain ⟨C, hC, hb⟩ := rpow_mul_exp_neg_mul_sq_le (m := (p : ℝ)) (b := 1 / 8)
    (Nat.cast_nonneg p) (by norm_num)
  refine ⟨2 ^ p * (1 + C), by positivity, fun s hs => ?_⟩
  have hb' := hb s hs
  rw [Real.rpow_natCast] at hb'
  have he : Real.exp (-s ^ 2 / 8) = Real.exp (-(1 / 8 * s ^ 2)) := by congr 1; ring
  rw [he]
  have hE : Real.exp (-(1 / 8 * s ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hE0 : 0 ≤ Real.exp (-(1 / 8 * s ^ 2)) := (Real.exp_pos _).le
  -- (1+s)^p ≤ 2^p (1 + s^p)
  have hpow : (1 + s) ^ p ≤ 2 ^ p * (1 + s ^ p) := by
    rcases le_total s 1 with h | h
    · have : (1 + s) ^ p ≤ 2 ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
      have : (0 : ℝ) ≤ 2 ^ p * s ^ p := by positivity
      nlinarith
    · have : (1 + s) ^ p ≤ (2 * s) ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
      rw [mul_pow] at this
      have : (0 : ℝ) ≤ 2 ^ p := by positivity
      nlinarith
  calc (1 + s) ^ p * Real.exp (-(1 / 8 * s ^ 2))
      ≤ 2 ^ p * (1 + s ^ p) * Real.exp (-(1 / 8 * s ^ 2)) := by gcongr
    _ = 2 ^ p * (Real.exp (-(1 / 8 * s ^ 2)) + s ^ p * Real.exp (-(1 / 8 * s ^ 2))) := by ring
    _ ≤ 2 ^ p * (1 + C) := by gcongr

/-- **G9 (B0169, "the periodized `q`-sum and its polynomial prefactor are uniformly
bounded").** For every `p` there is `C` such that, for every period `c` with `c² ≥ 2` and all
`q, η, λ`:
`∑_n (1 + |q-nc| + |η|)^p e^{-((q-nc)² + η²)/4} ≤ C e^{-λη + 2λ²}`. -/
theorem tsum_poly_periodized_gauss_tilt_le (p : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {c : ℝ}, 2 ≤ c ^ 2 → ∀ q η lam : ℝ,
      ∑' n : ℤ, (1 + |q - n * c| + |η|) ^ p * Real.exp (-((q - n * c) ^ 2 + η ^ 2) / 4) ≤
        C * Real.exp (-lam * η + 2 * lam ^ 2) := by
  obtain ⟨A, hA, hAb⟩ := one_add_pow_mul_exp_le p
  refine ⟨10 * A ^ 2, by positivity, ?_⟩
  intro c hc q η lam
  -- (1 + x + y)^p ≤ (1+x)^p (1+y)^p for x, y ≥ 0
  have hpt : ∀ n : ℤ, (1 + |q - n * c| + |η|) ^ p *
      Real.exp (-((q - n * c) ^ 2 + η ^ 2) / 4) ≤
      A * Real.exp (-(q - n * c) ^ 2 / (4 * 2)) * (A * Real.exp (-η ^ 2 / 8)) := by
    intro n
    set x := |q - n * c|
    set y := |η|
    have hx : 0 ≤ x := abs_nonneg _
    have hy : 0 ≤ y := abs_nonneg _
    have hxy : (1 + x + y) ^ p ≤ (1 + x) ^ p * (1 + y) ^ p := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by nlinarith) p
    have hsq1 : (q - n * c) ^ 2 = x ^ 2 := (sq_abs _).symm
    have hsq2 : η ^ 2 = y ^ 2 := (sq_abs _).symm
    have hexp : Real.exp (-((q - n * c) ^ 2 + η ^ 2) / 4) =
        (Real.exp (-x ^ 2 / 8) * Real.exp (-x ^ 2 / (4 * 2))) *
          (Real.exp (-y ^ 2 / 8) * Real.exp (-y ^ 2 / 8)) := by
      simp only [← Real.exp_add]; rw [hsq1, hsq2]; congr 1; ring
    rw [hexp]
    have h1 := hAb x hx
    have h2 := hAb y hy
    have e1 : Real.exp (-(q - n * c) ^ 2 / (4 * 2)) = Real.exp (-x ^ 2 / (4 * 2)) := by
      rw [hsq1]
    have e2 : Real.exp (-η ^ 2 / 8) = Real.exp (-y ^ 2 / 8) := by rw [hsq2]
    rw [e1, e2]
    have hpx : 0 ≤ (1 + x) ^ p := by positivity
    have hpy : 0 ≤ (1 + y) ^ p := by positivity
    calc (1 + x + y) ^ p * ((Real.exp (-x ^ 2 / 8) * Real.exp (-x ^ 2 / (4 * 2))) *
          (Real.exp (-y ^ 2 / 8) * Real.exp (-y ^ 2 / 8)))
        ≤ (1 + x) ^ p * (1 + y) ^ p * ((Real.exp (-x ^ 2 / 8) * Real.exp (-x ^ 2 / (4 * 2))) *
          (Real.exp (-y ^ 2 / 8) * Real.exp (-y ^ 2 / 8))) := by gcongr
      _ = ((1 + x) ^ p * Real.exp (-x ^ 2 / 8)) * Real.exp (-x ^ 2 / (4 * 2)) *
          (((1 + y) ^ p * Real.exp (-y ^ 2 / 8)) * Real.exp (-y ^ 2 / 8)) := by ring
      _ ≤ A * Real.exp (-x ^ 2 / (4 * 2)) * (A * Real.exp (-y ^ 2 / 8)) := by gcongr
  have hsum2 := summable_gauss_shift (a := 2) (c := c) (by norm_num) hc q
  have hmaj : Summable fun n : ℤ =>
      A * Real.exp (-(q - n * c) ^ 2 / (4 * 2)) * (A * Real.exp (-η ^ 2 / 8)) :=
    (hsum2.mul_left A).mul_right _
  have hsumL : Summable fun n : ℤ => (1 + |q - n * c| + |η|) ^ p *
      Real.exp (-((q - n * c) ^ 2 + η ^ 2) / 4) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hpt hmaj
  refine (hsumL.tsum_le_tsum hpt hmaj).trans ?_
  rw [tsum_mul_right, tsum_mul_left]
  have h10 := tsum_gauss_shift_le (a := 2) (c := c) (by norm_num) hc q
  -- e^{-η²/8} ≤ e^{-λη + 2λ²}
  have htilt : Real.exp (-η ^ 2 / 8) ≤ Real.exp (-lam * η + 2 * lam ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg (η - 4 * lam)])
  have h0 : 0 ≤ ∑' n : ℤ, Real.exp (-(q - n * c) ^ 2 / (4 * 2)) :=
    tsum_nonneg fun n => (Real.exp_pos _).le
  calc A * (∑' n : ℤ, Real.exp (-(q - n * c) ^ 2 / (4 * 2))) * (A * Real.exp (-η ^ 2 / 8))
      ≤ A * 10 * (A * Real.exp (-lam * η + 2 * lam ^ 2)) := by gcongr
    _ = 10 * A ^ 2 * Real.exp (-lam * η + 2 * lam ^ 2) := by ring

end UnforcedLeray.Gaussian
