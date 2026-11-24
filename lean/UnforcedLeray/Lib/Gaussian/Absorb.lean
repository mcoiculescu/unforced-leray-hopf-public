import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polynomial absorption into Gaussians and the supremum over time (INF22 G2)


§5 Layer G, target G2, used by bypass BP3 (the last step of the Gaussian derivative bound,
G1) and BP4 (`sup_{t>0} t^{-m/2} e^{-|x|²/(8t)} = C_m |x|^{-m}`, Oseen bounds, tex 3.7–3.8).
Manuscript uses: every "polynomial factor absorbed by the Gaussian" step, e.g. B0147
(tex 2217–2234), B0239 (tex 4133–4147), B0814–B0815 (tex 11888–11902).

Main results:
* `pow_mul_exp_neg_le_factorial`: `s^k e^{-s} ≤ k!` for `s ≥ 0`;
* `rpow_mul_exp_neg_le`: `s^p e^{-s} ≤ C_p` for `s ≥ 0`, `p ≥ 0`;
* `rpow_mul_exp_neg_mul_sq_le`: `u^m e^{-b u²} ≤ C` for `u ≥ 0`, `m ≥ 0`, `b > 0`;
* `rpow_mul_exp_le` (G2): `r^m e^{-r²/(4a)} ≤ C a^{m/2} e^{-r²/(8a)}`;
* `sup_time_le` (G2): `a^{-m/2} e^{-r²/(8a)} ≤ C r^{-m}`.
All constants depend only on the displayed exponents, never on `r`, `a`, `s`, `u`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open Real

/-- `s^k e^{-s} ≤ k!` for `s ≥ 0` (from `s^k/k! ≤ e^s`). -/
theorem pow_mul_exp_neg_le_factorial (k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    s ^ k * Real.exp (-s) ≤ (k.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (x := s) hs k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hf] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos s)]
  linarith [mul_comm (Real.exp s) (k.factorial : ℝ)]

/-- `s^p e^{-s} ≤ C_p` for all `s ≥ 0`, any real `p ≥ 0`. -/
theorem rpow_mul_exp_neg_le {p : ℝ} (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s → s ^ p * Real.exp (-s) ≤ C := by
  set k : ℕ := ⌈p⌉₊
  refine ⟨1 + k.factorial, by positivity, fun s hs => ?_⟩
  have he : 0 < Real.exp (-s) := Real.exp_pos _
  have he1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rcases le_total s 1 with h1 | h1
  · have : s ^ p ≤ 1 := Real.rpow_le_one hs h1 hp
    have hf : (0 : ℝ) ≤ k.factorial := by positivity
    nlinarith
  · have hpk : s ^ p ≤ s ^ (k : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil p)
    rw [Real.rpow_natCast] at hpk
    have := pow_mul_exp_neg_le_factorial k hs
    nlinarith

/-- `u^m e^{-b u²} ≤ C` for all `u ≥ 0` (`m ≥ 0`, `b > 0`). -/
theorem rpow_mul_exp_neg_mul_sq_le {m b : ℝ} (hm : 0 ≤ m) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 ≤ u → u ^ m * Real.exp (-(b * u ^ 2)) ≤ C := by
  obtain ⟨C₀, hC₀, hC⟩ := rpow_mul_exp_neg_le (p := m / 2) (by positivity)
  refine ⟨(b⁻¹) ^ (m / 2) * C₀, by positivity, fun u hu => ?_⟩
  set s := b * u ^ 2 with hs_def
  have hs : 0 ≤ s := by positivity
  have hu2 : u ^ m = (b⁻¹) ^ (m / 2) * s ^ (m / 2) := by
    rw [← Real.mul_rpow (by positivity) hs, hs_def, ← mul_assoc, inv_mul_cancel₀ hb.ne',
      one_mul, ← Real.rpow_natCast, ← Real.rpow_mul hu]
    congr 1; push_cast; ring
  rw [hu2, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC s hs) (by positivity)

/-- **G2, first half.** Polynomial absorption: `r^m e^{-r²/(4a)} ≤ C a^{m/2} e^{-r²/(8a)}`
for `r ≥ 0`, `a > 0`, with `C` depending only on `m ≥ 0`. -/
theorem rpow_mul_exp_le (m : ℝ) (hm : 0 ≤ m) : ∃ C : ℝ, 0 < C ∧ ∀ r a : ℝ, 0 ≤ r → 0 < a →
    r ^ m * Real.exp (-r ^ 2 / (4 * a)) ≤ C * a ^ (m / 2) * Real.exp (-r ^ 2 / (8 * a)) := by
  obtain ⟨C, hC0, hC⟩ := rpow_mul_exp_neg_mul_sq_le (m := m) (b := 1 / 8) hm (by norm_num)
  refine ⟨C, hC0, fun r a hr ha => ?_⟩
  set u := r / Real.sqrt a with hu_def
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hu : 0 ≤ u := div_nonneg hr hsa.le
  have hr_eq : r = Real.sqrt a * u := by rw [hu_def]; field_simp
  have hrm : r ^ m = a ^ (m / 2) * u ^ m := by
    rw [hr_eq, Real.mul_rpow hsa.le hu, Real.sqrt_eq_rpow, ← Real.rpow_mul ha.le]
    congr 2; ring
  have hsq : r ^ 2 / (8 * a) = 1 / 8 * u ^ 2 := by
    rw [hr_eq, mul_pow, Real.sq_sqrt ha.le]; field_simp
  have hsplit : Real.exp (-r ^ 2 / (4 * a)) =
      Real.exp (-(1 / 8 * u ^ 2)) * Real.exp (-r ^ 2 / (8 * a)) := by
    rw [← Real.exp_add]; congr 1
    rw [neg_div, neg_div, ← hsq]; field_simp; ring
  rw [hrm, hsplit]
  have h1 := hC u hu
  have h2 : 0 ≤ a ^ (m / 2) := by positivity
  have h3 : 0 < Real.exp (-r ^ 2 / (8 * a)) := Real.exp_pos _
  calc a ^ (m / 2) * u ^ m * (Real.exp (-(1 / 8 * u ^ 2)) * Real.exp (-r ^ 2 / (8 * a)))
      = a ^ (m / 2) * (u ^ m * Real.exp (-(1 / 8 * u ^ 2))) * Real.exp (-r ^ 2 / (8 * a)) := by
        ring
    _ ≤ a ^ (m / 2) * C * Real.exp (-r ^ 2 / (8 * a)) := by gcongr
    _ = C * a ^ (m / 2) * Real.exp (-r ^ 2 / (8 * a)) := by ring

/-- **G2, second half.** Supremum over time: `a^{-m/2} e^{-r²/(8a)} ≤ C r^{-m}` for
`a, r > 0` and `m ≥ 0` (the scoping note asks `m > 0`; `m ≥ 0` is weaker). -/
theorem sup_time_le (m : ℝ) (hm : 0 ≤ m) : ∃ C : ℝ, 0 < C ∧ ∀ a r : ℝ, 0 < a → 0 < r →
    a ^ (-m / 2) * Real.exp (-r ^ 2 / (8 * a)) ≤ C * r ^ (-m) := by
  obtain ⟨C, hC0, hC⟩ := rpow_mul_exp_neg_mul_sq_le (m := m) (b := 1 / 8) hm (by norm_num)
  refine ⟨C, hC0, fun a r ha hr => ?_⟩
  set u := r / Real.sqrt a with hu_def
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hu : 0 < u := div_pos hr hsa
  have hr_eq : r = Real.sqrt a * u := by rw [hu_def]; field_simp
  have hsq : r ^ 2 / (8 * a) = 1 / 8 * u ^ 2 := by
    rw [hr_eq, mul_pow, Real.sq_sqrt ha.le]; field_simp
  have ha_eq : a ^ (-m / 2) = u ^ m * r ^ (-m) := by
    rw [hu_def, Real.div_rpow hr.le hsa.le, Real.rpow_neg hr.le, Real.sqrt_eq_rpow,
      ← Real.rpow_mul ha.le, show -m / 2 = -(1 / 2 * m) by ring, Real.rpow_neg ha.le]
    have h1 : 0 < r ^ m := Real.rpow_pos_of_pos hr m
    have h2 : 0 < a ^ (1 / 2 * m) := Real.rpow_pos_of_pos ha _
    field_simp
  rw [ha_eq, neg_div, hsq]
  have := hC u hu.le
  have hr' : 0 < r ^ (-m) := Real.rpow_pos_of_pos hr _
  calc u ^ m * r ^ (-m) * Real.exp (-(1 / 8 * u ^ 2))
      = (u ^ m * Real.exp (-(1 / 8 * u ^ 2))) * r ^ (-m) := by ring
    _ ≤ C * r ^ (-m) := by gcongr

end UnforcedLeray.Gaussian
