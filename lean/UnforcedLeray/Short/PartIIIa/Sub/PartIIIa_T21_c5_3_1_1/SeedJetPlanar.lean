import UnforcedLeray.Lib.PlanarSectors.AngularTwo
import UnforcedLeray.Lib.ComplexODEC.Velocity

/-!
# Weighted second jets of Cartesian angular-two functions (helper for `PartIII-a:T21/c5/3/1/1/1`)

Source `the November 2 reference manuscript`
lines 593-610 and 2891-2897: the planar dual kernels have `O(|y|^{-2-j})`-type decay of their
fixed derivatives.  In Cartesian form the kernels are `w ↦ w² β(|w|²)` (composed with a
conjugation), and this file proves the analytic core: if `β`, `β'`, `β''` decay like
`(1+s)^{-2}`, `(1+s)^{-3}`, `(1+s)^{-3}` on `s ≥ 0`, then the first derivative of
`F(w) = w² β(|w|²)` is `O((1+|w|)^{-3})` and the second is `O((1+|w|)^{-2})`.

The second-derivative bound uses Leibniz' rule for `w² · β(|w|²)` and Faà di Bruno's bound for
`β(|w|²)` applied to the shifted profile `β - β(|w|²)`, whose value at `|w|²` vanishes, so only
`β'` and `β''` enter; the first derivative of `|w|²` is bounded by `2|w|`.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.SeedJet2Aux

/-- `‖D(|x|²)(w)‖ ≤ 2|w|`. -/
theorem norm_fderiv_normSq_le (w : ℂ) :
    ‖fderiv ℝ (fun x : ℂ => ‖x‖ ^ 2) w‖ ≤ 2 * ‖w‖ := by
  rw [fderiv_norm_sq_apply]
  refine norm_nsmul_le.trans ?_
  rw [innerSL_apply_norm]
  norm_num

/-- Refined Faà di Bruno bound for `β(|x|²)` at orders `1, 2`: only `β'` and `β''` enter. -/
theorem norm_iteratedFDeriv_comp_normSq_shift_le {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β)
    {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ 2) (w : ℂ) :
    ‖iteratedFDeriv ℝ n (fun x : ℂ => β (‖x‖ ^ 2)) w‖ ≤
      n.factorial * (‖deriv β (‖w‖ ^ 2)‖ + ‖deriv (deriv β) (‖w‖ ^ 2)‖) *
        (2 * (1 + ‖w‖)) ^ n := by
  set g : ℝ → ℂ := fun t => β t - β (‖w‖ ^ 2) with hg
  have hgc : ContDiff ℝ 2 g := hβ.sub contDiff_const
  have hN : ContDiff ℝ 2 (fun x : ℂ => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hcomp : (fun x : ℂ => β (‖x‖ ^ 2)) =
      (g ∘ fun x : ℂ => ‖x‖ ^ 2) + fun _ => β (‖w‖ ^ 2) := by
    funext x
    simp [g]
  have hn2' : ((n : ℕ) : ℕ∞ω) ≤ 2 := by exact_mod_cast hn2
  have hshift : iteratedFDeriv ℝ n (fun x : ℂ => β (‖x‖ ^ 2)) w =
      iteratedFDeriv ℝ n (g ∘ fun x : ℂ => ‖x‖ ^ 2) w := by
    rw [hcomp, iteratedFDeriv_add_apply ((hgc.comp hN).contDiffAt.of_le hn2') contDiffAt_const,
      iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, add_zero]
  rw [hshift]
  have hdg : deriv g = deriv β := by
    funext t
    simp only [g]
    exact deriv_sub_const _
  refine norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := g) (f := fun x : ℂ => ‖x‖ ^ 2) (N := 2)
    hgc hN hn2' w ?_ ?_
  · intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hi2 : i ≤ 2 := hi.trans hn2
    interval_cases i
    · rw [iteratedDeriv_zero]
      simp only [g, sub_self, norm_zero]
      positivity
    · rw [iteratedDeriv_one, hdg]
      exact le_add_of_nonneg_right (norm_nonneg _)
    · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hdg]
      exact le_add_of_nonneg_left (norm_nonneg _)
  · intro i hi1 hi2
    have hi2' : i ≤ 2 := hi2.trans hn2
    interval_cases i
    · rw [pow_one, norm_iteratedFDeriv_one]
      exact (norm_fderiv_normSq_le w).trans (by linarith [norm_nonneg w])
    · refine (Planar.norm_iteratedFDeriv_normSq_le 2 w).trans (le_of_eq ?_)
      ring

/-- **Weighted jets of `w ↦ w² β(|w|²)`**: if `‖β(s)‖(1+s)² ≤ B`, `‖β'(s)‖(1+s)³ ≤ B` and
`‖β''(s)‖(1+s)³ ≤ B` on `s ≥ 0`, then `‖DF(w)‖(1+|w|)³ ≤ 24 B` and
`‖D²F(w)‖(1+|w|)² ≤ 272 B`. -/
theorem angularTwo_jet2_decay {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β) {B : ℝ}
    (h0 : ∀ s, 0 ≤ s → ‖β s‖ * (1 + s) ^ 2 ≤ B)
    (h1 : ∀ s, 0 ≤ s → ‖deriv β s‖ * (1 + s) ^ 3 ≤ B)
    (h2 : ∀ s, 0 ≤ s → ‖deriv (deriv β) s‖ * (1 + s) ^ 3 ≤ B) (w : ℂ) :
    ‖fderiv ℝ (fun w : ℂ => w ^ 2 * β (‖w‖ ^ 2)) w‖ * (1 + ‖w‖) ^ 3 ≤ 24 * B ∧
    ‖iteratedFDeriv ℝ 2 (fun w : ℂ => w ^ 2 * β (‖w‖ ^ 2)) w‖ * (1 + ‖w‖) ^ 2 ≤ 272 * B := by
  set r : ℝ := ‖w‖ with hr
  set s : ℝ := r ^ 2 with hs
  set a : ℝ := 1 + r with ha
  set v : ℝ := 1 + s with hv
  have hr0 : 0 ≤ r := norm_nonneg w
  have hs0 : 0 ≤ s := by positivity
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hv0 : 0 ≤ v := by positivity
  have hav : a ^ 2 ≤ 2 * v := by simp only [a, v, s]; nlinarith [sq_nonneg (r - 1)]
  have hra : r ≤ a := by linarith
  have ha4 : a ^ 4 ≤ 4 * v ^ 2 := by
    have : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg v]
  have ha6 : a ^ 6 ≤ 8 * v ^ 3 := by
    have : a ^ 6 = (a ^ 2) ^ 3 := by ring
    rw [this]
    have h := pow_le_pow_left₀ (by positivity) hav 3
    nlinarith [h]
  have hY := h0 s hs0
  have hX1 := h1 s hs0
  have hX2 := h2 s hs0
  have hB0 : 0 ≤ B := le_trans (by positivity) (h0 0 le_rfl)
  constructor
  · -- first derivative
    have hd := ComplexODEC.norm_fderiv_angularTwo_le (B := β)
      (hβ.differentiable (by norm_num)) w
    rw [← hr, ← hs] at hd
    have e1 : 2 * r * ‖β s‖ * a ^ 3 ≤ 8 * B := by
      have : 2 * r * ‖β s‖ * a ^ 3 ≤ 2 * ‖β s‖ * a ^ 4 := by
        have : r * a ^ 3 ≤ a ^ 4 := by
          have := mul_le_mul_of_nonneg_right hra (pow_nonneg ha0 3)
          calc r * a ^ 3 ≤ a * a ^ 3 := this
            _ = a ^ 4 := by ring
        nlinarith [norm_nonneg (β s)]
      refine this.trans ?_
      have : 2 * ‖β s‖ * a ^ 4 ≤ 2 * ‖β s‖ * (4 * v ^ 2) := by
        gcongr
      nlinarith [norm_nonneg (β s)]
    have e2 : 2 * r ^ 3 * ‖deriv β s‖ * a ^ 3 ≤ 16 * B := by
      have hr3 : r ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ hr0 hra 3
      have : 2 * r ^ 3 * ‖deriv β s‖ * a ^ 3 ≤ 2 * ‖deriv β s‖ * a ^ 6 := by
        have : r ^ 3 * a ^ 3 ≤ a ^ 6 := by
          have := mul_le_mul_of_nonneg_right hr3 (pow_nonneg ha0 3)
          calc r ^ 3 * a ^ 3 ≤ a ^ 3 * a ^ 3 := this
            _ = a ^ 6 := by ring
        nlinarith [norm_nonneg (deriv β s)]
      refine this.trans ?_
      have : 2 * ‖deriv β s‖ * a ^ 6 ≤ 2 * ‖deriv β s‖ * (8 * v ^ 3) := by
        gcongr
      nlinarith [norm_nonneg (deriv β s)]
    calc ‖fderiv ℝ (fun w : ℂ => w ^ 2 * β (‖w‖ ^ 2)) w‖ * a ^ 3
        ≤ (2 * r * ‖β s‖ + 2 * r ^ 3 * ‖deriv β s‖) * a ^ 3 := by gcongr
      _ = 2 * r * ‖β s‖ * a ^ 3 + 2 * r ^ 3 * ‖deriv β s‖ * a ^ 3 := by ring
      _ ≤ 8 * B + 16 * B := add_le_add e1 e2
      _ = 24 * B := by ring
  · -- second derivative
    have hP : ContDiff ℝ 2 (fun y : ℂ => y ^ 2) := contDiff_id.pow 2
    have hQ : ContDiff ℝ 2 (fun y : ℂ => β (‖y‖ ^ 2)) := hβ.comp (contDiff_norm_sq ℝ)
    have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fun y : ℂ => y ^ 2)
      (g := fun y : ℂ => β (‖y‖ ^ 2)) (N := 2) hP hQ w (n := 2) le_rfl
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero] at hL
    have hc21 : ((Nat.choose 2 1 : ℕ) : ℝ) = 2 := by norm_num
    rw [hc21] at hL
    have hP0 := Planar.norm_iteratedFDeriv_sq_le 0 w
    have hP1 := Planar.norm_iteratedFDeriv_sq_le 1 w
    have hP2 := Planar.norm_iteratedFDeriv_sq_le 2 w
    have hQ1 := norm_iteratedFDeriv_comp_normSq_shift_le hβ (n := 1) le_rfl (by norm_num) w
    have hQ2 := norm_iteratedFDeriv_comp_normSq_shift_le hβ (n := 2) (by norm_num) le_rfl w
    have hQ0 : ‖iteratedFDeriv ℝ 0 (fun y : ℂ => β (‖y‖ ^ 2)) w‖ = ‖β s‖ := by
      rw [norm_iteratedFDeriv_zero]
    rw [← hr, ← ha] at hP0 hP1 hP2
    rw [← hr, ← hs, ← ha] at hQ1 hQ2
    have h21 : (2 : ℕ) - 1 = 1 := rfl
    rw [h21] at hL
    set X : ℝ := ‖deriv β s‖ + ‖deriv (deriv β) s‖ with hX
    have hX0 : 0 ≤ X := by positivity
    have hXv : X * v ^ 3 ≤ 2 * B := by
      have : X * v ^ 3 = ‖deriv β s‖ * v ^ 3 + ‖deriv (deriv β) s‖ * v ^ 3 := by ring
      rw [this]
      linarith
    rw [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at hQ1
    rw [Nat.factorial_two, Nat.cast_ofNat] at hQ2
    rw [pow_zero, one_mul] at hP0
    rw [pow_one] at hP1
    -- the three Leibniz terms
    have t1 : ‖iteratedFDeriv ℝ 0 (fun y : ℂ => y ^ 2) w‖ *
        ‖iteratedFDeriv ℝ 2 (fun y : ℂ => β (‖y‖ ^ 2)) w‖ * a ^ 2 ≤ 128 * B := by
      have hA : ‖iteratedFDeriv ℝ 0 (fun y : ℂ => y ^ 2) w‖ *
          ‖iteratedFDeriv ℝ 2 (fun y : ℂ => β (‖y‖ ^ 2)) w‖ * a ^ 2 ≤
          a ^ 2 * (2 * X * (2 * a) ^ 2) * a ^ 2 := by
        gcongr
      refine hA.trans ?_
      have : a ^ 2 * (2 * X * (2 * a) ^ 2) * a ^ 2 = 8 * X * a ^ 6 := by ring
      rw [this]
      calc 8 * X * a ^ 6 ≤ 8 * X * (8 * v ^ 3) := by gcongr
        _ = 64 * (X * v ^ 3) := by ring
        _ ≤ 64 * (2 * B) := by gcongr
        _ = 128 * B := by ring
    have t2 : 2 * ‖iteratedFDeriv ℝ 1 (fun y : ℂ => y ^ 2) w‖ *
        ‖iteratedFDeriv ℝ 1 (fun y : ℂ => β (‖y‖ ^ 2)) w‖ * a ^ 2 ≤ 128 * B := by
      have hA : 2 * ‖iteratedFDeriv ℝ 1 (fun y : ℂ => y ^ 2) w‖ *
          ‖iteratedFDeriv ℝ 1 (fun y : ℂ => β (‖y‖ ^ 2)) w‖ * a ^ 2 ≤
          2 * (2 * a ^ 2) * (X * (2 * a)) * a ^ 2 := by
        gcongr
      refine hA.trans ?_
      have : 2 * (2 * a ^ 2) * (X * (2 * a)) * a ^ 2 = 8 * X * a ^ 5 := by ring
      rw [this]
      have ha56 : a ^ 5 ≤ a ^ 6 := pow_le_pow_right₀ ha1 (by norm_num)
      calc 8 * X * a ^ 5 ≤ 8 * X * (8 * v ^ 3) := by
            gcongr
            exact ha56.trans ha6
        _ = 64 * (X * v ^ 3) := by ring
        _ ≤ 64 * (2 * B) := by gcongr
        _ = 128 * B := by ring
    have t3 : ‖iteratedFDeriv ℝ 2 (fun y : ℂ => y ^ 2) w‖ *
        ‖iteratedFDeriv ℝ 0 (fun y : ℂ => β (‖y‖ ^ 2)) w‖ * a ^ 2 ≤ 16 * B := by
      rw [hQ0]
      have hA : ‖iteratedFDeriv ℝ 2 (fun y : ℂ => y ^ 2) w‖ * ‖β s‖ * a ^ 2 ≤
          (2 ^ 2 * a ^ 2) * ‖β s‖ * a ^ 2 := by
        gcongr
      refine hA.trans ?_
      calc 2 ^ 2 * a ^ 2 * ‖β s‖ * a ^ 2 = 4 * ‖β s‖ * a ^ 4 := by ring
        _ ≤ 4 * ‖β s‖ * (4 * v ^ 2) := by gcongr
        _ = 16 * (‖β s‖ * v ^ 2) := by ring
        _ ≤ 16 * B := by gcongr
    calc ‖iteratedFDeriv ℝ 2 (fun w : ℂ => w ^ 2 * β (‖w‖ ^ 2)) w‖ * a ^ 2
        ≤ (‖iteratedFDeriv ℝ 0 (fun y : ℂ => y ^ 2) w‖ *
            ‖iteratedFDeriv ℝ 2 (fun y : ℂ => β (‖y‖ ^ 2)) w‖ +
          2 * ‖iteratedFDeriv ℝ 1 (fun y : ℂ => y ^ 2) w‖ *
            ‖iteratedFDeriv ℝ 1 (fun y : ℂ => β (‖y‖ ^ 2)) w‖ +
          ‖iteratedFDeriv ℝ 2 (fun y : ℂ => y ^ 2) w‖ *
            ‖iteratedFDeriv ℝ 0 (fun y : ℂ => β (‖y‖ ^ 2)) w‖) * a ^ 2 :=
          mul_le_mul_of_nonneg_right hL (by positivity)
      _ = ‖iteratedFDeriv ℝ 0 (fun y : ℂ => y ^ 2) w‖ *
            ‖iteratedFDeriv ℝ 2 (fun y : ℂ => β (‖y‖ ^ 2)) w‖ * a ^ 2 +
          2 * ‖iteratedFDeriv ℝ 1 (fun y : ℂ => y ^ 2) w‖ *
            ‖iteratedFDeriv ℝ 1 (fun y : ℂ => β (‖y‖ ^ 2)) w‖ * a ^ 2 +
          ‖iteratedFDeriv ℝ 2 (fun y : ℂ => y ^ 2) w‖ *
            ‖iteratedFDeriv ℝ 0 (fun y : ℂ => β (‖y‖ ^ 2)) w‖ * a ^ 2 := by ring
      _ ≤ 128 * B + 128 * B + 16 * B := add_le_add (add_le_add t1 t2) t3
      _ = 272 * B := by ring

end UnforcedLeray.Short.IIIa.SeedJet2Aux
