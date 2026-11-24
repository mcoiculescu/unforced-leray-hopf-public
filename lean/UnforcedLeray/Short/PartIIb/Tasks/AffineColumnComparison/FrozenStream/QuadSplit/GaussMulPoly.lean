import UnforcedLeray.Short.PartIIb.Sub.G4_2_2_1

/-!
# Part II-b, task `PartII-b:G4/2/2/1/1`: `GaussMulPoly`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: the Leibniz rule `iteratedDerivWithin_mul` on the open set `(0,∞)`, the triangle inequality,
uniform constants over the finitely many orders `< n` (induction on `n`), and the absorption
`r^N e^{-κ r²} ≤ A e^{-(κ/2) r²}` for `r ≥ 1` (from `x^N/N! ≤ e^x`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

theorem gaussMulPoly : UnforcedLeray.Short.IIb.GaussMulPoly := by
  -- Leibniz bound, pointwise on `(0,∞)`
  have leib : ∀ (f g : ℝ → ℂ) (j : ℕ) (r : ℝ), 0 < r → ContDiffOn ℝ ∞ f (Ioi 0) →
      ContDiffOn ℝ ∞ g (Ioi 0) →
      ‖iteratedDeriv j (fun s => f s * g s) r‖ ≤
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (‖iteratedDeriv i f r‖ * ‖iteratedDeriv (j - i) g r‖) := by
    intro f g j r hr hf hg
    have hx : r ∈ Ioi (0 : ℝ) := hr
    have hfw : ContDiffWithinAt ℝ j f (Ioi 0) r := (hf r hx).of_le (by exact_mod_cast le_top)
    have hgw : ContDiffWithinAt ℝ j g (Ioi 0) r := (hg r hx).of_le (by exact_mod_cast le_top)
    have hL : iteratedDerivWithin j (f * g) (Ioi 0) r = ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℂ) * iteratedDerivWithin i f (Ioi 0) r *
          iteratedDerivWithin (j - i) g (Ioi 0) r :=
      iteratedDerivWithin_mul hx isOpen_Ioi.uniqueDiffOn hfw hgw
    have hfi : ∀ i : ℕ, iteratedDerivWithin i f (Ioi 0) r = iteratedDeriv i f r :=
      fun i => iteratedDerivWithin_of_isOpen (n := i) isOpen_Ioi hx
    have hgi : ∀ i : ℕ, iteratedDerivWithin i g (Ioi 0) r = iteratedDeriv i g r :=
      fun i => iteratedDerivWithin_of_isOpen (n := i) isOpen_Ioi hx
    have hfgi : ∀ i : ℕ, iteratedDerivWithin i (f * g) (Ioi 0) r = iteratedDeriv i (f * g) r :=
      fun i => iteratedDerivWithin_of_isOpen (n := i) isOpen_Ioi hx
    simp only [hfi, hgi, hfgi] at hL
    show ‖iteratedDeriv j (f * g) r‖ ≤ _
    rw [hL]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    exact le_of_eq (by ring)
  -- monotonicity of Gaussian bounds in the constant and the rate
  have gmono : ∀ (x C C' κ κ' r : ℝ), x ≤ C * Real.exp (-(κ * r ^ 2)) → 0 ≤ C' → C ≤ C' →
      κ' ≤ κ → x ≤ C' * Real.exp (-(κ' * r ^ 2)) := by
    intro x C C' κ κ' r hx hC' hCC hκκ
    calc x ≤ C * Real.exp (-(κ * r ^ 2)) := hx
      _ ≤ C' * Real.exp (-(κ * r ^ 2)) := mul_le_mul_of_nonneg_right hCC (Real.exp_pos _).le
      _ ≤ C' * Real.exp (-(κ' * r ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (neg_le_neg (mul_le_mul_of_nonneg_right hκκ (sq_nonneg r)))) hC'
  -- polynomial monotonicity
  have pmono : ∀ (x C C' : ℝ) (N N' : ℕ) (r : ℝ), x ≤ C * r ^ N → 0 ≤ C' → C ≤ C' →
      N ≤ N' → 1 ≤ r → x ≤ C' * r ^ N' := by
    intro x C C' N N' r hx hC' hCC hNN hr
    have hr0 : (0 : ℝ) ≤ r := by linarith
    calc x ≤ C * r ^ N := hx
      _ ≤ C' * r ^ N := mul_le_mul_of_nonneg_right hCC (pow_nonneg hr0 _)
      _ ≤ C' * r ^ N' := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hNN) hC'
  -- uniform Gaussian constants over orders `< n`
  have unifG : ∀ (f : ℝ → ℂ) (n : ℕ), (∀ i < n, GaussAt f i) →
      ∃ (C κ : ℝ), 0 < κ ∧ ∀ i < n, ∀ r : ℝ, 1 ≤ r →
        ‖iteratedDeriv i f r‖ ≤ C * Real.exp (-(κ * r ^ 2)) := by
    intro f n
    induction n with
    | zero => intro _; exact ⟨0, 1, one_pos, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro h
      obtain ⟨C, κ, hκ, hb⟩ := ih (fun i hi => h i (by omega))
      obtain ⟨Cn, κn, hκn, hbn⟩ := h n (by omega)
      refine ⟨|C| + |Cn|, min κ κn, lt_min hκ hκn, fun i hi r hr => ?_⟩
      have hC0 : 0 ≤ |C| + |Cn| := add_nonneg (abs_nonneg _) (abs_nonneg _)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · exact gmono _ C _ κ _ r (hb i hi' r hr) hC0
          (by linarith [le_abs_self C, abs_nonneg Cn]) (min_le_left _ _)
      · exact gmono _ Cn _ κn _ r (hbn r hr) hC0
          (by linarith [le_abs_self Cn, abs_nonneg C]) (min_le_right _ _)
  -- uniform polynomial constants over orders `< n`
  have unifP : ∀ (g : ℝ → ℂ) (n : ℕ), (∀ i < n, PolyAt g i) →
      ∃ (C : ℝ) (N : ℕ), ∀ i < n, ∀ r : ℝ, 1 ≤ r →
        ‖iteratedDeriv i g r‖ ≤ C * r ^ N := by
    intro g n
    induction n with
    | zero => intro _; exact ⟨0, 0, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro h
      obtain ⟨C, N, hb⟩ := ih (fun i hi => h i (by omega))
      obtain ⟨Cn, Nn, hbn⟩ := h n (by omega)
      refine ⟨|C| + |Cn|, max N Nn, fun i hi r hr => ?_⟩
      have hC0 : 0 ≤ |C| + |Cn| := add_nonneg (abs_nonneg _) (abs_nonneg _)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · exact pmono _ C _ N _ r (hb i hi' r hr) hC0
          (by linarith [le_abs_self C, abs_nonneg Cn]) (le_max_left _ _) hr
      · exact pmono _ Cn _ Nn _ r (hbn r hr) hC0
          (by linarith [le_abs_self Cn, abs_nonneg C]) (le_max_right _ _) hr
  -- absorption: `r^N e^{-κ r²} ≤ A e^{-(κ/2) r²}` on `[1,∞)`
  have absorb : ∀ (N : ℕ) (κ : ℝ), 0 < κ → ∃ A : ℝ, ∀ r : ℝ, 1 ≤ r →
      r ^ N * Real.exp (-(κ * r ^ 2)) ≤ A * Real.exp (-((κ / 2) * r ^ 2)) := by
    intro N κ hκ
    refine ⟨(2 / κ) ^ N * (N.factorial : ℝ), fun r hr => ?_⟩
    have hr0 : (0 : ℝ) ≤ r := by linarith
    have hx0 : 0 ≤ (κ / 2) * r ^ 2 := mul_nonneg (by linarith) (sq_nonneg r)
    set x := (κ / 2) * r ^ 2 with hx_def
    have hkey : Real.exp (-(κ * r ^ 2)) = Real.exp (-x) * Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
      rw [hx_def]
      ring
    have hrN : r ^ N ≤ (2 / κ) ^ N * x ^ N := by
      have h1 : r ^ N ≤ (r ^ 2) ^ N := by
        calc r ^ N ≤ r ^ (2 * N) := pow_le_pow_right₀ hr (by omega)
          _ = (r ^ 2) ^ N := by rw [pow_mul]
      have h2 : r ^ 2 = (2 / κ) * x := by
        rw [hx_def]
        field_simp
      rw [h2, mul_pow] at h1
      exact h1
    have hfac : x ^ N ≤ (N.factorial : ℝ) * Real.exp x := by
      have h := Real.pow_div_factorial_le_exp x hx0 N
      rw [div_le_iff₀ (by positivity)] at h
      linarith [mul_comm (Real.exp x) (N.factorial : ℝ)]
    have hprod : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      simp
    have hmain : r ^ N * Real.exp (-x) ≤ (2 / κ) ^ N * (N.factorial : ℝ) := by
      calc r ^ N * Real.exp (-x) ≤ ((2 / κ) ^ N * x ^ N) * Real.exp (-x) :=
            mul_le_mul_of_nonneg_right hrN (Real.exp_pos _).le
        _ ≤ ((2 / κ) ^ N * ((N.factorial : ℝ) * Real.exp x)) * Real.exp (-x) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfac
                (pow_nonneg (div_nonneg (by norm_num) hκ.le) N)) (Real.exp_pos _).le
        _ = (2 / κ) ^ N * (N.factorial : ℝ) := by
            linear_combination ((2 / κ) ^ N * (N.factorial : ℝ)) * hprod
    calc r ^ N * Real.exp (-(κ * r ^ 2)) = (r ^ N * Real.exp (-x)) * Real.exp (-x) := by
          rw [hkey]
          ring
      _ ≤ ((2 / κ) ^ N * (N.factorial : ℝ)) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right hmain (Real.exp_pos _).le
  -- the main estimate
  intro f g n hf hg hG hP j hj
  obtain ⟨CF, κ, hκ, hFb⟩ := unifG f n hG
  obtain ⟨CP, N, hPb⟩ := unifP g n hP
  obtain ⟨A, hAb⟩ := absorb N κ hκ
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (|CF| * |CP| * A), κ / 2,
    half_pos hκ, fun r hr => ?_⟩
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * (‖iteratedDeriv i f r‖ * ‖iteratedDeriv (j - i) g r‖) ≤
        ((j.choose i : ℝ) * (|CF| * |CP| * A)) * Real.exp (-((κ / 2) * r ^ 2)) := by
    intro i hi
    have hi' : i < j + 1 := Finset.mem_range.mp hi
    have h1 := hFb i (by omega) r hr
    have h2 := hPb (j - i) (by omega) r hr
    have hf1 : ‖iteratedDeriv i f r‖ ≤ |CF| * Real.exp (-(κ * r ^ 2)) :=
      h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
    have hg1 : ‖iteratedDeriv (j - i) g r‖ ≤ |CP| * r ^ N :=
      h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hr0 _))
    have hc : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
    have hA' := hAb r hr
    calc (j.choose i : ℝ) * (‖iteratedDeriv i f r‖ * ‖iteratedDeriv (j - i) g r‖)
        ≤ (j.choose i : ℝ) * ((|CF| * Real.exp (-(κ * r ^ 2))) * (|CP| * r ^ N)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hf1 hg1 (norm_nonneg _)
              (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)) hc
      _ = ((j.choose i : ℝ) * (|CF| * |CP|)) * (r ^ N * Real.exp (-(κ * r ^ 2))) := by ring
      _ ≤ ((j.choose i : ℝ) * (|CF| * |CP|)) * (A * Real.exp (-((κ / 2) * r ^ 2))) :=
          mul_le_mul_of_nonneg_left hA'
            (mul_nonneg hc (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      _ = ((j.choose i : ℝ) * (|CF| * |CP| * A)) * Real.exp (-((κ / 2) * r ^ 2)) := by ring
  refine (leib f g j r hrpos hf hg).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum hterm

end UnforcedLeray.Short.IIb
