import UnforcedLeray.Short.PartIIIb.StatementsB

/-!
# Basic facts on the amplitudes `F_±(s,t)` (source 4368-4372, 4376-4411)

`Fpm j lam κ ν s t = exp(λ_j (z(s) - z(t))) (a(s)/a(t))^{κ_j}` with `a(s) = 1 + νs > 0`.
We prove: `F_j(t,t) = 1`, `F_j(s,t) ≠ 0` for `s,t ≥ 0`, and `|F_-(s,t)| = |F_+(s,t)|`
(the conjugate pair has equal modulus because `Re λ̄ = Re λ`, `Re κ̄ = Re κ`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

lemma aOf_pos_of_nonneg (ν s : ℝ) (hν : 0 < ν) (hs : 0 ≤ s) : 0 < aOf ν s := by
  unfold aOf
  have := mul_nonneg hν.le hs
  linarith

lemma fpm_true_eq (lam κ : ℂ) (ν s t : ℝ) :
    Fpm true lam κ ν s t
      = Complex.exp (lam * ((zOf ν s - zOf ν t : ℝ) : ℂ))
          * ((aOf ν s / aOf ν t : ℝ) : ℂ) ^ κ := rfl

lemma fpm_false_eq (lam κ : ℂ) (ν s t : ℝ) :
    Fpm false lam κ ν s t
      = Complex.exp ((starRingEnd ℂ) lam * ((zOf ν s - zOf ν t : ℝ) : ℂ))
          * ((aOf ν s / aOf ν t : ℝ) : ℂ) ^ (starRingEnd ℂ) κ := rfl

lemma fpm_self_eq_one (j : Bool) (lam κ : ℂ) (ν t : ℝ) (ha : aOf ν t ≠ 0) :
    Fpm j lam κ ν t t = 1 := by
  cases j
  · rw [fpm_false_eq, sub_self, div_self ha]
    simp
  · rw [fpm_true_eq, sub_self, div_self ha]
    simp

lemma fpm_ne_zero_of_pos (j : Bool) (lam κ : ℂ) (ν s t : ℝ) (hr : 0 < aOf ν s / aOf ν t) :
    Fpm j lam κ ν s t ≠ 0 := by
  have hc : ((aOf ν s / aOf ν t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  cases j
  · rw [fpm_false_eq]
    exact mul_ne_zero (Complex.exp_ne_zero _)
      (by rw [Complex.cpow_def_of_ne_zero hc]; exact Complex.exp_ne_zero _)
  · rw [fpm_true_eq]
    exact mul_ne_zero (Complex.exp_ne_zero _)
      (by rw [Complex.cpow_def_of_ne_zero hc]; exact Complex.exp_ne_zero _)

lemma fpm_norm_formula (l k : ℂ) (ν s t : ℝ) (hr : 0 < aOf ν s / aOf ν t) :
    ‖Complex.exp (l * ((zOf ν s - zOf ν t : ℝ) : ℂ))
        * ((aOf ν s / aOf ν t : ℝ) : ℂ) ^ k‖
      = Real.exp (l.re * (zOf ν s - zOf ν t)) * (aOf ν s / aOf ν t) ^ k.re := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hr]
  congr 2
  simp [Complex.mul_re]

theorem fpm_facts (ν : ℝ) (hν : 0 < ν) (lam κ : ℂ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∀ j : Bool, Fpm j lam κ ν t t = 1) ∧ (∀ j : Bool, Fpm j lam κ ν s t ≠ 0) ∧
      ‖Fpm false lam κ ν s t‖ = ‖Fpm true lam κ ν s t‖ := by
  have hr : (0 : ℝ) < aOf ν s / aOf ν t :=
    div_pos (aOf_pos_of_nonneg ν s hν hs) (aOf_pos_of_nonneg ν t hν ht)
  refine ⟨fun j => fpm_self_eq_one j lam κ ν t (aOf_pos_of_nonneg ν t hν ht).ne', ?_, ?_⟩
  · intro j
    exact fpm_ne_zero_of_pos j lam κ ν s t hr
  · rw [fpm_false_eq, fpm_true_eq, fpm_norm_formula _ _ ν s t hr,
      fpm_norm_formula _ _ ν s t hr, Complex.conj_re, Complex.conj_re]

end UnforcedLeray.Short.PartIIIb
