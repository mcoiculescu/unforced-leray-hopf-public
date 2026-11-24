import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# B0104, helper: a Gronwall inequality without measurability

Helper for blueprint unit `B0104` (`lem:compact-duhamel`, `paper/main.tex` lines 1586-1621).
The proof sketch there says "The Dyson series have uniform exponential majorants". We replace the
termwise Dyson majorant by an iteration of the Duhamel inequality against continuous exponential
majorants (a Bielecki-weight argument), which needs no measurability of the unknown function:
the integral is only ever taken of an explicit continuous majorant `g`.

* `integral_mul_exp_mul_sub`: `∫ r in s..t, c e^{λ(r-s)} = c (e^{λ(t-s)} - 1) / λ`.
* `gronwall_family`: if a family `φ i` is bounded by `C` on `[s, s+B]` and, for every continuous
  nonnegative `g ≥ φ i` on `[s,t]`, `φ i t ≤ a + L ∫_s^t g`, then
  `φ i t ≤ 2 a e^{(2L+1)(t-s)}` on `[s, s+B]`.
* `mul_div_small`: `C · (ε / (2(|C|+1))) < ε`, used to turn `≤ C η` bounds into `< ε` bounds.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Real

namespace UnforcedLeray.B0104

/-- `∫ r in s..t, c e^{λ(r-s)} = c (e^{λ(t-s)} - 1) / λ` for `λ > 0`. -/
theorem integral_mul_exp_mul_sub {s t lam : ℝ} (c : ℝ) (hlam : 0 < lam) :
    ∫ r in s..t, c * exp (lam * (r - s)) = c * (exp (lam * (t - s)) - 1) / lam := by
  have hderiv : ∀ r ∈ uIcc s t,
      HasDerivAt (fun r => c * exp (lam * (r - s)) / lam) (c * exp (lam * (r - s))) r := by
    intro r _
    have h1 : HasDerivAt (fun r => lam * (r - s)) lam r := by
      simpa using ((hasDerivAt_id r).sub_const s).const_mul lam
    have h2 := (h1.exp.const_mul c).div_const lam
    exact h2.congr_deriv (by rw [mul_div_assoc, mul_div_cancel_right₀ _ hlam.ne'])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [sub_self, mul_zero, Real.exp_zero]
  ring

/-- **Gronwall inequality without measurability**, for a family of functions.

Let `a, L ≥ 0`, and let `φ i : ℝ → ℝ` (`i ∈ I`) be bounded by `C` on `[s, s+B]`. Suppose that for
every continuous `g`, nonnegative on `[s,t]` and dominating every `φ i` on `[s,t]`, one has
`φ i t ≤ a + L ∫_s^t g`. Then `φ i t ≤ 2 a e^{(2L+1)(t-s)}` on `[s, s+B]`. -/
theorem gronwall_family {I : Type*} (φ : I → ℝ → ℝ) {s B a L C : ℝ} (ha : 0 ≤ a) (hL : 0 ≤ L)
    (hC : ∀ i, ∀ t, s ≤ t → t ≤ s + B → φ i t ≤ C)
    (h : ∀ g : ℝ → ℝ, Continuous g → ∀ t, s ≤ t → t ≤ s + B →
      (∀ r, s ≤ r → r ≤ t → 0 ≤ g r) → (∀ i, ∀ r, s ≤ r → r ≤ t → φ i r ≤ g r) →
      ∀ i, φ i t ≤ a + L * ∫ r in s..t, g r) :
    ∀ i, ∀ t, s ≤ t → t ≤ s + B → φ i t ≤ 2 * a * exp ((2 * L + 1) * (t - s)) := by
  have hlam : 0 < 2 * L + 1 := by linarith
  have hc₀ : 0 ≤ max C 0 := le_max_right _ _
  have key : ∀ k : ℕ, ∀ i, ∀ t, s ≤ t → t ≤ s + B →
      φ i t ≤ (2 * a + max C 0 * (1 / 2) ^ k) * exp ((2 * L + 1) * (t - s)) := by
    intro k
    induction k with
    | zero =>
      intro i t h1 h2
      have he : 1 ≤ exp ((2 * L + 1) * (t - s)) :=
        one_le_exp (mul_nonneg hlam.le (by linarith))
      calc φ i t ≤ C := hC i t h1 h2
        _ ≤ max C 0 := le_max_left _ _
        _ ≤ (2 * a + max C 0 * (1 / 2) ^ 0) * 1 := by simp; linarith
        _ ≤ (2 * a + max C 0 * (1 / 2) ^ 0) * exp ((2 * L + 1) * (t - s)) :=
          mul_le_mul_of_nonneg_left he (by simp; linarith)
    | succ k ih =>
      intro i t h1 h2
      have hc : 0 ≤ 2 * a + max C 0 * (1 / 2) ^ k := by positivity
      have hg := h (fun r => (2 * a + max C 0 * (1 / 2) ^ k) * exp ((2 * L + 1) * (r - s)))
        (by fun_prop) t h1 h2 (fun r _ _ => by positivity)
        (fun j r hr1 hr2 => ih j r hr1 (by linarith)) i
      rw [integral_mul_exp_mul_sub _ hlam] at hg
      set c := 2 * a + max C 0 * (1 / 2) ^ k with hc_def
      set E := exp ((2 * L + 1) * (t - s)) with hE_def
      have he : 1 ≤ E := one_le_exp (mul_nonneg hlam.le (by linarith))
      have h3 : L * (c * (E - 1) / (2 * L + 1)) ≤ c / 2 * E := by
        have hrw : L * (c * (E - 1) / (2 * L + 1)) = L * c * (E - 1) / (2 * L + 1) := by ring
        rw [hrw, div_le_iff₀ hlam]
        nlinarith [mul_nonneg hc hL, mul_nonneg hc (by linarith : (0 : ℝ) ≤ E),
          mul_nonneg (mul_nonneg hc hL) (by linarith : (0 : ℝ) ≤ E)]
      have h4 : a ≤ a * E := by nlinarith
      calc φ i t ≤ a + L * (c * (E - 1) / (2 * L + 1)) := hg
        _ ≤ a * E + c / 2 * E := by linarith
        _ = (2 * a + max C 0 * (1 / 2) ^ (k + 1)) * E := by rw [hc_def, pow_succ]; ring
  intro i t h1 h2
  have h0 : Tendsto (fun k : ℕ => max C 0 * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (max C 0)
    rwa [mul_zero] at this
  have ht : Tendsto (fun k : ℕ => (2 * a + max C 0 * (1 / 2 : ℝ) ^ k) *
      exp ((2 * L + 1) * (t - s))) atTop (𝓝 ((2 * a + 0) * exp ((2 * L + 1) * (t - s)))) :=
    (tendsto_const_nhds.add h0).mul_const _
  rw [add_zero] at ht
  exact ge_of_tendsto' ht fun k => key k i t h1 h2

/-- `C · (ε / (2(|C|+1))) < ε` for `ε > 0`. -/
theorem mul_div_small (C : ℝ) {ε : ℝ} (hε : 0 < ε) : C * (ε / (2 * (|C| + 1))) < ε := by
  have hpos : 0 < 2 * (|C| + 1) := by positivity
  calc C * (ε / (2 * (|C| + 1))) ≤ |C| * (ε / (2 * (|C| + 1))) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ = |C| * ε / (2 * (|C| + 1)) := by ring
    _ < ε := by
      rw [div_lt_iff₀ hpos]
      nlinarith [abs_nonneg C]

theorem small_pos {C ε : ℝ} (hε : 0 < ε) : 0 < ε / (2 * (|C| + 1)) := by positivity

end UnforcedLeray.B0104
