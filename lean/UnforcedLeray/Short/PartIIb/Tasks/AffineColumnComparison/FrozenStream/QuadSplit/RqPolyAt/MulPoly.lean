import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_2_1_5

/-!
# Part II-b, task `PartII-b:G4/2/2/1/5/1`: `PolyMulPoly`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: the Leibniz rule `iteratedDerivWithin_mul` on `(0,∞)`, the triangle inequality, uniform
polynomial constants over the finitely many orders `< n`, and `r^N * r^M = r^(N+M)` for `r ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

theorem polyMulPoly : UnforcedLeray.Short.IIb.PolyMulPoly := by
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
  -- polynomial monotonicity
  have pmono : ∀ (x C C' : ℝ) (N N' : ℕ) (r : ℝ), x ≤ C * r ^ N → 0 ≤ C' → C ≤ C' →
      N ≤ N' → 1 ≤ r → x ≤ C' * r ^ N' := by
    intro x C C' N N' r hx hC' hCC hNN hr
    have hr0 : (0 : ℝ) ≤ r := by linarith
    calc x ≤ C * r ^ N := hx
      _ ≤ C' * r ^ N := mul_le_mul_of_nonneg_right hCC (pow_nonneg hr0 _)
      _ ≤ C' * r ^ N' := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hNN) hC'
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
  -- the main estimate
  intro f g n hf hg hF hG j hj
  obtain ⟨CF, NF, hFb⟩ := unifP f n hF
  obtain ⟨CG, NG, hGb⟩ := unifP g n hG
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (|CF| * |CG|), NF + NG,
    fun r hr => ?_⟩
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * (‖iteratedDeriv i f r‖ * ‖iteratedDeriv (j - i) g r‖) ≤
        ((j.choose i : ℝ) * (|CF| * |CG|)) * r ^ (NF + NG) := by
    intro i hi
    have hi' : i < j + 1 := Finset.mem_range.mp hi
    have h1 := hFb i (by omega) r hr
    have h2 := hGb (j - i) (by omega) r hr
    have hf1 : ‖iteratedDeriv i f r‖ ≤ |CF| * r ^ NF :=
      h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hr0 _))
    have hg1 : ‖iteratedDeriv (j - i) g r‖ ≤ |CG| * r ^ NG :=
      h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hr0 _))
    have hc : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
    calc (j.choose i : ℝ) * (‖iteratedDeriv i f r‖ * ‖iteratedDeriv (j - i) g r‖)
        ≤ (j.choose i : ℝ) * ((|CF| * r ^ NF) * (|CG| * r ^ NG)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hf1 hg1 (norm_nonneg _)
              (mul_nonneg (abs_nonneg _) (pow_nonneg hr0 _))) hc
      _ = ((j.choose i : ℝ) * (|CF| * |CG|)) * r ^ (NF + NG) := by ring
  refine (leib f g j r hrpos hf hg).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum hterm

end UnforcedLeray.Short.IIb
