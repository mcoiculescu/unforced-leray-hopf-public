import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_5_1_2
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Leaf B: lattice Gaussian sums (SP 2357-2358)

Proves `GaussLatticeSum`.  Re-centre at the nearest lattice point: `k₀ = round(-ξ/c)`, so
`|ξ + k₀ c| ≤ c/2`; for `k = j + k₀` one has `(ξ + kc)² ≥ j²c²/4`, hence the `k`-th term of
`∑_k e^{-b(ξ+kc)²}` is dominated by the Gaussian `e^{-(bc²/4) j²}` in `j = k - k₀`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- The Gaussian `m ↦ e^{-a m²}` is summable over `ℤ` for `a > 0` (Jacobi theta bound). -/
private lemma gl_summable_gauss (a : ℝ) (ha : 0 < a) :
    Summable (fun m : ℤ => Real.exp (-(a * (m : ℝ) ^ 2))) := by
  have hT : 0 < a / Real.pi := div_pos ha Real.pi_pos
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0 hT 0
  refine h.congr fun m => ?_
  simp only [pow_zero, one_mul]
  congr 1
  field_simp <;> ring

/-- Re-centring: for `c > 0` there is an integer `k₀` with `|ξ + k₀ c| ≤ c/2`. -/
private lemma gl_recentre (ξ c : ℝ) (hc : 0 < c) :
    ∃ k0 : ℤ, |ξ + (k0 : ℝ) * c| ≤ c / 2 := by
  refine ⟨round (-ξ / c), ?_⟩
  have h := abs_sub_round (-ξ / c)
  have e : ξ + ((round (-ξ / c) : ℤ) : ℝ) * c = -(c * (-ξ / c - ((round (-ξ / c) : ℤ) : ℝ))) := by
    field_simp
    ring
  rw [e, abs_neg, abs_mul, abs_of_pos hc]
  have := mul_le_mul_of_nonneg_left h hc.le
  linarith

/-- Comparison of one term after re-centring: `k = j + k₀`. -/
private lemma gl_term_le (b c ξ : ℝ) (hb : 0 < b) (hc : 0 < c) (k0 : ℤ)
    (hk0 : |ξ + (k0 : ℝ) * c| ≤ c / 2) (k : ℤ) :
    Real.exp (-(b * (ξ + (k : ℝ) * c) ^ 2)) ≤
      Real.exp (-((b * c ^ 2 / 4) * ((k - k0 : ℤ) : ℝ) ^ 2)) := by
  apply Real.exp_le_exp.2
  have hkj : ξ + (k : ℝ) * c = (ξ + (k0 : ℝ) * c) + ((k - k0 : ℤ) : ℝ) * c := by
    push_cast; ring
  rw [hkj]
  set x : ℝ := ξ + (k0 : ℝ) * c with hx
  set j : ℤ := k - k0 with hj
  have hsq : (j : ℝ) ^ 2 * c ^ 2 / 4 ≤ (x + (j : ℝ) * c) ^ 2 := by
    rcases eq_or_ne j 0 with h0 | h0
    · rw [h0]; push_cast; nlinarith [sq_nonneg x]
    · have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
        have : (1 : ℤ) ≤ |j| := Int.one_le_abs h0
        exact_mod_cast this
      have hA : |(j : ℝ) * c| = |(j : ℝ)| * c := by rw [abs_mul, abs_of_pos hc]
      have htri : |(j : ℝ) * c| - |x + (j : ℝ) * c| ≤ |x| := by
        have := abs_sub_abs_le_abs_sub ((j : ℝ) * c) (x + (j : ℝ) * c)
        rw [show (j : ℝ) * c - (x + (j : ℝ) * c) = -x by ring, abs_neg] at this
        exact this
      have hL : |(j : ℝ)| * c / 2 ≤ |x + (j : ℝ) * c| := by
        have hx2 : |x| ≤ c / 2 := hk0
        nlinarith
      have hsqL : (|(j : ℝ)| * c / 2) ^ 2 ≤ |x + (j : ℝ) * c| ^ 2 :=
        pow_le_pow_left₀ (by positivity) hL 2
      rw [sq_abs] at hsqL
      have e1 : (|(j : ℝ)| * c / 2) ^ 2 = (j : ℝ) ^ 2 * c ^ 2 / 4 := by
        rw [div_pow, mul_pow, sq_abs]; ring
      linarith
  have hmul := mul_le_mul_of_nonneg_left hsq hb.le
  nlinarith

/-- Summability of the re-centred lattice Gaussian. -/
private lemma gl_summable (b c ξ : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Summable (fun k : ℤ => Real.exp (-(b * (ξ + (k : ℝ) * c) ^ 2))) := by
  obtain ⟨k0, hk0⟩ := gl_recentre ξ c hc
  have hs := gl_summable_gauss (b * c ^ 2 / 4) (by positivity)
  have hs' : Summable (fun k : ℤ => Real.exp (-((b * c ^ 2 / 4) * ((k - k0 : ℤ) : ℝ) ^ 2))) :=
    (Equiv.subRight k0).summable_iff.2 hs
  exact Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le)
    (fun k => gl_term_le b c ξ hb hc k0 hk0 k) hs'

/-- **Leaf B: lattice Gaussian sums** (SP 2357-2358). -/
theorem gaussLatticeSum : UnforcedLeray.Short.IIIa.GaussLatticeSum := by
  refine ⟨fun b c hb hc ξ => gl_summable b c ξ hb hc, ?_⟩
  refine ⟨∑' j : ℤ, Real.exp (-((1 / 64 : ℝ) * (j : ℝ) ^ 2)), ?_⟩
  intro c hc1 ξ
  have hc : 0 < c := by linarith
  obtain ⟨k0, hk0⟩ := gl_recentre ξ c hc
  have hs := gl_summable_gauss (1 / 64 : ℝ) (by norm_num)
  have hsg : Summable (fun k : ℤ => Real.exp (-((1 / 64 : ℝ) * ((k - k0 : ℤ) : ℝ) ^ 2))) :=
    (Equiv.subRight k0).summable_iff.2 hs
  have hle : ∀ k : ℤ, Real.exp (-((ξ + (k : ℝ) * c) ^ 2 / 16)) ≤
      Real.exp (-((1 / 64 : ℝ) * ((k - k0 : ℤ) : ℝ) ^ 2)) := by
    intro k
    have h1 := gl_term_le (1 / 16) c ξ (by norm_num) hc k0 hk0 k
    have hsq : (0 : ℝ) ≤ ((k - k0 : ℤ) : ℝ) ^ 2 := sq_nonneg _
    have hc2 : (1 : ℝ) ≤ c ^ 2 := by nlinarith
    have h2 : Real.exp (-((1 / 16 : ℝ) * c ^ 2 / 4 * ((k - k0 : ℤ) : ℝ) ^ 2)) ≤
        Real.exp (-((1 / 64 : ℝ) * ((k - k0 : ℤ) : ℝ) ^ 2)) := by
      apply Real.exp_le_exp.2
      nlinarith
    have e : Real.exp (-((ξ + (k : ℝ) * c) ^ 2 / 16)) =
        Real.exp (-((1 / 16 : ℝ) * (ξ + (k : ℝ) * c) ^ 2)) := by
      congr 1; ring
    rw [e]
    exact h1.trans h2
  have hLs : Summable (fun k : ℤ => Real.exp (-((ξ + (k : ℝ) * c) ^ 2 / 16))) :=
    Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) hle hsg
  calc ∑' k : ℤ, Real.exp (-((ξ + (k : ℝ) * c) ^ 2 / 16))
      ≤ ∑' k : ℤ, Real.exp (-((1 / 64 : ℝ) * ((k - k0 : ℤ) : ℝ) ^ 2)) :=
        Summable.tsum_le_tsum hle hLs hsg
    _ = ∑' j : ℤ, Real.exp (-((1 / 64 : ℝ) * (j : ℝ) ^ 2)) :=
        (Equiv.subRight k0).tsum_eq (fun j : ℤ => Real.exp (-((1 / 64 : ℝ) * (j : ℝ) ^ 2)))

end UnforcedLeray.Short.IIIa
