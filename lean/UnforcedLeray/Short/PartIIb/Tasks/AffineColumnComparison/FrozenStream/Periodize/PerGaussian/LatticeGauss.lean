import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_3_3
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Part II-b, task `PartII-b:G4/2/3/3/1`: uniform lattice Gaussian sum

Source of record: `the November 2 reference manuscript`, lines 2349-2358.

Let `k₀ = ⌊-x₁/c⌋`, so `t₀ = x₁ + k₀c ∈ (-c, 0]`. With `m = k - k₀`, `x₁ + kc = t₀ + mc`, and
`(t₀ + mc)² ≥ m²/2 - 1` for every integer `m`. Hence the `k`-th term is at most
`e^κ e^{-(κ/2) m²}`, a summable sequence reindexed by `k ↦ k - k₀`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The Gaussian `m ↦ e^{-a m²}` is summable over `ℤ` for `a > 0`. -/
lemma gauss_summable_int (a : ℝ) (ha : 0 < a) :
    Summable (fun m : ℤ => Real.exp (-(a * (m : ℝ) ^ 2))) := by
  have hT : 0 < a / Real.pi := div_pos ha Real.pi_pos
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0 hT 0
  refine h.congr fun m => ?_
  simp only [pow_zero, one_mul]
  congr 1
  field_simp <;> ring

/-- Key quadratic bound: for `c ≥ 1` and `-c < t₀ ≤ 0`, `(t₀ + m c)² ≥ m²/2 - 1` for `m ∈ ℤ`. -/
lemma sq_shift_ge (c t₀ : ℝ) (hc : 1 ≤ c) (h1 : -c < t₀) (h2 : t₀ ≤ 0) (n : ℤ) :
    ((n : ℝ) ^ 2) / 2 - 1 ≤ (t₀ + (n : ℝ) * c) ^ 2 := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hn' : (n : ℝ) ≤ -1 := by
      have : n ≤ -1 := by omega
      exact_mod_cast this
    have hnc : (n : ℝ) * c ≤ n := by nlinarith
    have hu : t₀ + (n : ℝ) * c ≤ (n : ℝ) := by linarith
    have hu' : t₀ + (n : ℝ) * c ≤ 0 := by linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - (t₀ + (n : ℝ) * c))
      (by linarith : (0 : ℝ) ≤ -((n : ℝ)) - (t₀ + (n : ℝ) * c) + 2 * (-(n : ℝ)))]
  · subst hn
    simp only [Int.cast_zero]
    nlinarith [sq_nonneg t₀]
  · have hn' : (1 : ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := by omega
      exact_mod_cast this
    have hnc : (n : ℝ) - 1 ≤ (n : ℝ) * c - c := by nlinarith
    have hu1 : (n : ℝ) - 1 ≤ t₀ + (n : ℝ) * c := by linarith
    have hu0 : 0 ≤ (n : ℝ) - 1 := by linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (t₀ + (n : ℝ) * c) - ((n : ℝ) - 1))
      (by linarith : (0 : ℝ) ≤ (t₀ + (n : ℝ) * c) + ((n : ℝ) - 1)), sq_nonneg ((n : ℝ) - 2)]

theorem latticeGaussSum : UnforcedLeray.Short.IIb.LatticeGaussSum := by
  intro κ hκ
  have hgs : Summable (fun m : ℤ => Real.exp (-((κ / 2) * (m : ℝ) ^ 2))) :=
    gauss_summable_int (κ / 2) (by linarith)
  refine ⟨Real.exp κ * ∑' m : ℤ, Real.exp (-((κ / 2) * (m : ℝ) ^ 2)), fun c hc x₁ => ?_⟩
  have hc0 : 0 < c := by linarith
  set k₀ : ℤ := ⌊-x₁ / c⌋ with hk₀
  set t₀ : ℝ := x₁ + (k₀ : ℝ) * c with ht₀
  have hfl1 : (k₀ : ℝ) ≤ -x₁ / c := Int.floor_le _
  have hfl2 : -x₁ / c < (k₀ : ℝ) + 1 := Int.lt_floor_add_one _
  have ht1 : t₀ ≤ 0 := by
    have h := mul_le_mul_of_nonneg_right hfl1 hc0.le
    rw [div_mul_cancel₀ _ hc0.ne'] at h
    linarith
  have ht2 : -c < t₀ := by
    have h := mul_lt_mul_of_pos_right hfl2 hc0
    rw [div_mul_cancel₀ _ hc0.ne'] at h
    linarith
  have hkey : ∀ k : ℤ, Real.exp (-(κ * (x₁ + k * c) ^ 2)) ≤
      Real.exp κ * Real.exp (-((κ / 2) * ((k - k₀ : ℤ) : ℝ) ^ 2)) := by
    intro k
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hx : x₁ + (k : ℝ) * c = t₀ + ((k - k₀ : ℤ) : ℝ) * c := by
      rw [ht₀]; push_cast; ring
    rw [hx]
    have hsq := sq_shift_ge c t₀ hc ht2 ht1 (k - k₀)
    have hm := mul_le_mul_of_nonneg_left hsq hκ.le
    nlinarith
  have hsh : Summable (fun k : ℤ => Real.exp κ * Real.exp (-((κ / 2) * ((k - k₀ : ℤ) : ℝ) ^ 2))) := by
    apply Summable.mul_left
    exact (Equiv.subRight k₀).summable_iff.mpr hgs
  have hf : Summable (fun k : ℤ => Real.exp (-(κ * (x₁ + k * c) ^ 2))) :=
    Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) hkey hsh
  refine ⟨hf, ?_⟩
  calc ∑' k : ℤ, Real.exp (-(κ * (x₁ + k * c) ^ 2))
      ≤ ∑' k : ℤ, Real.exp κ * Real.exp (-((κ / 2) * ((k - k₀ : ℤ) : ℝ) ^ 2)) :=
        hf.tsum_le_tsum hkey hsh
    _ = Real.exp κ * ∑' k : ℤ, Real.exp (-((κ / 2) * ((k - k₀ : ℤ) : ℝ) ^ 2)) := tsum_mul_left
    _ = Real.exp κ * ∑' m : ℤ, Real.exp (-((κ / 2) * (m : ℝ) ^ 2)) := by
        congr 1
        exact (Equiv.subRight k₀).tsum_eq (fun m : ℤ => Real.exp (-((κ / 2) * (m : ℝ) ^ 2)))

end UnforcedLeray.Short.IIb
