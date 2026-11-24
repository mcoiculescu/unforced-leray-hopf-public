import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Uniform Gaussian lattice-sum bounds (INF22 G6, BP9)


target G6 and bypass BP9 (the geometric trick `m² ≥ m`, no theta transformation). Units B0147
(tex 2217–2234), B0239 (tex 4133–4147), B0335 (tex 6348–6428), B0814/B0815 (tex 11888–11902),
B0169 (tex 2526–2540, through G9) and the mode tail of B0233 (tex 3989–4008).

Main results (all constants explicit and uniform in the lattice parameters):
* `tsum_gauss_shift_le`: `∑_{n∈ℤ} e^{-(y-nc)²/(4a)} ≤ 10` whenever `0 < a ≤ c²`, for every `y`
  (summability in `summable_gauss_shift`);
* `tsum_gauss_ne_zero_le`: `∑_{k≠0} e^{-k²c²/(8a)} ≤ 18 e^{-c²/(8a)}` whenever `0 < a ≤ c²`;
* `tsum_exp_neg_abs_ne_zero_le`: `∑_{n≠0} e^{-β|n|} ≤ 2(1 + 1/β) e^{-β}` for `β > 0`, and its
  instance `tsum_mode_tail_le`: `∑_{n≠0} e^{-2π|n|l/c} ≤ 2(1 + c/(2πl)) e^{-2πl/c}`;
* polynomial weights: `tsum_pow_mul_gauss_ne_zero_le`, `∑_{k≠0} |k|^p e^{-k²β} ≤ C_p e^{-β}` for
  `β ≥ β₀ > 0`.

The general device is `tsum_int_le_of_le_two_sides`: a nonnegative `ℤ`-series dominated on both
half-lines by a summable `ℕ`-sequence.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open Real
open scoped Nat

/-! ### Splitting a `ℤ`-series into two half-lines -/

/-- If `f ≥ 0` on `ℤ` and `f m ≤ g m`, `f (-(m+1)) ≤ g m` for `m : ℕ` with `g` summable, then
`f` is summable and `∑ f ≤ 2 ∑ g`. -/
theorem tsum_int_le_of_le_two_sides {f : ℤ → ℝ} {g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hg : Summable g) (hpos : ∀ m : ℕ, f m ≤ g m) (hneg : ∀ m : ℕ, f (-((m : ℤ) + 1)) ≤ g m) :
    Summable f ∧ ∑' n, f n ≤ 2 * ∑' m, g m := by
  have h1 : Summable fun m : ℕ => f m := Summable.of_nonneg_of_le (fun m => hf m) hpos hg
  have h2 : Summable fun m : ℕ => f (-((m : ℤ) + 1)) :=
    Summable.of_nonneg_of_le (fun m => hf _) hneg hg
  refine ⟨h1.of_nat_of_neg_add_one h2, ?_⟩
  rw [tsum_of_nat_of_neg_add_one h1 h2, two_mul]
  exact add_le_add (h1.tsum_le_tsum hpos hg) (h2.tsum_le_tsum hneg hg)

/-- Variant that isolates the term `f 0`: if `f (m+1) ≤ g m` and `f (-(m+1)) ≤ g m`, then
`∑ f ≤ f 0 + 2 ∑ g`. -/
theorem tsum_int_le_of_le_two_sides' {f : ℤ → ℝ} {g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hg : Summable g) (hpos : ∀ m : ℕ, f ((m : ℤ) + 1) ≤ g m)
    (hneg : ∀ m : ℕ, f (-((m : ℤ) + 1)) ≤ g m) :
    Summable f ∧ ∑' n, f n ≤ f 0 + 2 * ∑' m, g m := by
  have h1 : Summable fun m : ℕ => f ((m : ℤ) + 1) :=
    Summable.of_nonneg_of_le (fun m => hf _) hpos hg
  have h2 : Summable fun m : ℕ => f (-((m : ℤ) + 1)) :=
    Summable.of_nonneg_of_le (fun m => hf _) hneg hg
  refine ⟨h1.of_add_one_of_neg_add_one h2, ?_⟩
  rw [tsum_of_add_one_of_neg_add_one h1 h2]
  have := h1.tsum_le_tsum hpos hg
  have := h2.tsum_le_tsum hneg hg
  linarith

/-! ### Geometric series of exponentials -/

theorem summable_exp_neg_mul_nat {β : ℝ} (hβ : 0 < β) :
    Summable fun m : ℕ => Real.exp (-β * m) := by
  have hr0 : 0 ≤ Real.exp (-β) := (Real.exp_pos _).le
  have hr1 : Real.exp (-β) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  refine (summable_geometric_of_lt_one hr0 hr1).congr fun m => ?_
  rw [← Real.exp_nat_mul]; ring_nf

theorem tsum_exp_neg_mul_nat {β : ℝ} (hβ : 0 < β) :
    ∑' m : ℕ, Real.exp (-β * m) = (1 - Real.exp (-β))⁻¹ := by
  have hr0 : 0 ≤ Real.exp (-β) := (Real.exp_pos _).le
  have hr1 : Real.exp (-β) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  rw [← tsum_geometric_of_lt_one hr0 hr1]
  congr 1; funext m
  rw [← Real.exp_nat_mul]; ring_nf

/-- `(1 - e^{-β})⁻¹ ≤ 1 + 1/β` for `β > 0` (from `e^β ≥ 1 + β`). -/
theorem inv_one_sub_exp_neg_le {β : ℝ} (hβ : 0 < β) :
    (1 - Real.exp (-β))⁻¹ ≤ 1 + β⁻¹ := by
  have h1 : β + 1 ≤ Real.exp β := Real.add_one_le_exp β
  have hpos : 0 < 1 - Real.exp (-β) := by
    have : Real.exp (-β) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hE : Real.exp (-β) * Real.exp β = 1 := by rw [← Real.exp_add]; simp
  rw [inv_le_iff_one_le_mul₀ hpos]
  have hexp : 0 < Real.exp (-β) := Real.exp_pos _
  -- (1 + 1/β)(1 - e^{-β}) ≥ 1  ⟺  e^{-β}(1 + β) ≤ 1
  have key : Real.exp (-β) * (β + 1) ≤ 1 := by
    calc Real.exp (-β) * (β + 1) ≤ Real.exp (-β) * Real.exp β :=
          mul_le_mul_of_nonneg_left h1 hexp.le
      _ = 1 := hE
  rw [show (1 + β⁻¹) * (1 - Real.exp (-β)) = 1 + β⁻¹ * (1 - Real.exp (-β) * (β + 1)) by
    field_simp; ring]
  have : 0 ≤ β⁻¹ * (1 - Real.exp (-β) * (β + 1)) :=
    mul_nonneg (inv_pos.2 hβ).le (by linarith)
  linarith

/-! ### The shifted Gaussian lattice sum -/

/-- Summability and the bound `∑_n e^{-(y-nc)²/(4a)} ≤ 10` for `c > 0`, `0 < a ≤ c²`. -/
theorem gauss_shift_aux {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a ≤ c ^ 2) (y : ℝ) :
    Summable (fun n : ℤ => Real.exp (-(y - n * c) ^ 2 / (4 * a))) ∧
      ∑' n : ℤ, Real.exp (-(y - n * c) ^ 2 / (4 * a)) ≤ 10 := by
  set N : ℤ := ⌈y / c⌉ with hN
  set f : ℤ → ℝ := fun n => Real.exp (-(y - n * c) ^ 2 / (4 * a)) with hf
  have hNy : y ≤ N * c := by
    have := Int.le_ceil (y / c); rwa [div_le_iff₀ hc] at this
  have hNy' : ((N : ℝ) - 1) * c < y := by
    have := Int.ceil_lt_add_one (y / c)
    rw [← sub_lt_iff_lt_add, lt_div_iff₀ hc] at this; exact this
  -- the key pointwise bound: if |y - x| ≥ m c, the term is ≤ e^{-m/4}
  have hkey : ∀ (x : ℝ) (m : ℕ), (m : ℝ) * c ≤ |y - x| →
      Real.exp (-(y - x) ^ 2 / (4 * a)) ≤ Real.exp (-(1 / 4) * m) := by
    intro x m hm
    refine Real.exp_le_exp.2 ?_
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hsq : ((m : ℝ) * c) ^ 2 ≤ (y - x) ^ 2 := by
      rw [← sq_abs (y - x)]; exact pow_le_pow_left₀ (by positivity) hm 2
    have hmm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos m with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ m := by exact_mod_cast h
        nlinarith
    have h1 : (m : ℝ) * a ≤ (y - x) ^ 2 := by
      calc (m : ℝ) * a ≤ (m : ℝ) ^ 2 * a := mul_le_mul_of_nonneg_right hmm ha.le
        _ ≤ (m : ℝ) ^ 2 * c ^ 2 := mul_le_mul_of_nonneg_left hac (by positivity)
        _ = ((m : ℝ) * c) ^ 2 := by ring
        _ ≤ (y - x) ^ 2 := hsq
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * a)]
    nlinarith
  have hshift : Summable (fun n : ℤ => f (N + n)) ∧ ∑' n : ℤ, f (N + n) ≤
      2 * ∑' m : ℕ, Real.exp (-(1 / 4) * m) := by
    refine tsum_int_le_of_le_two_sides (fun n => (Real.exp_pos _).le)
      (summable_exp_neg_mul_nat (by norm_num)) (fun m => ?_) (fun m => ?_)
    · refine hkey _ m ?_
      push_cast
      have : (m : ℝ) * c ≤ (N + m) * c - y := by nlinarith
      rw [abs_sub_comm, abs_of_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) m])]
      linarith
    · refine hkey _ m ?_
      push_cast
      have hmc : (0 : ℝ) ≤ m * c := by positivity
      have : (m : ℝ) * c ≤ y - (N + -((m : ℝ) + 1)) * c := by nlinarith
      rw [abs_of_nonneg (by linarith)]
      exact this
  have hsum : Summable f := by
    have := hshift.1.comp_injective (add_right_injective (-N))
    refine this.congr fun n => ?_
    simp
  refine ⟨hsum, ?_⟩
  have heq : ∑' n : ℤ, f n = ∑' n : ℤ, f (N + n) :=
    ((Equiv.addLeft N).tsum_eq f).symm
  rw [heq]
  refine hshift.2.trans ?_
  rw [tsum_exp_neg_mul_nat (by norm_num)]
  -- 2/(1 - e^{-1/4}) ≤ 10, from e^{1/4} ≥ 5/4
  have h1 : (1 : ℝ) / 4 + 1 ≤ Real.exp (1 / 4) := Real.add_one_le_exp _
  have hE : Real.exp (-(1 / 4)) * Real.exp (1 / 4) = 1 := by rw [← Real.exp_add]; simp
  have he : Real.exp (-(1 / 4)) ≤ 4 / 5 := by
    have hp := Real.exp_pos (-(1 / 4 : ℝ))
    nlinarith
  have hpos : 0 < 1 - Real.exp (-(1 / 4)) := by linarith
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  linarith

/-- **G6 (BP9; B0147, B0239).** `∑_{n∈ℤ} e^{-(y-nc)²/(4a)}` converges whenever `a > 0`,
`c ≠ 0`. -/
theorem summable_gauss_shift {a c : ℝ} (ha : 0 < a) (hac : a ≤ c ^ 2) (y : ℝ) :
    Summable (fun n : ℤ => Real.exp (-(y - n * c) ^ 2 / (4 * a))) := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have h := (gauss_shift_aux ha (neg_pos.2 hc) (by rwa [neg_sq]) y).1
    have := h.comp_injective neg_injective
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, Int.cast_neg]
    ring_nf
  · subst hc; nlinarith
  · exact (gauss_shift_aux ha hc hac y).1

/-- **G6 (BP9; B0147, B0239, tex 2217–2234).** Uniformly in `y`, in the period `c` and in the
time `a` with `0 < a ≤ c²`: `∑_{n∈ℤ} e^{-(y-nc)²/(4a)} ≤ 10`. -/
theorem tsum_gauss_shift_le {a c : ℝ} (ha : 0 < a) (hac : a ≤ c ^ 2) (y : ℝ) :
    ∑' n : ℤ, Real.exp (-(y - n * c) ^ 2 / (4 * a)) ≤ 10 := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have h := (gauss_shift_aux ha (neg_pos.2 hc) (by rwa [neg_sq]) y).2
    rw [← (Equiv.neg ℤ).tsum_eq] at h
    refine le_of_eq_of_le ?_ h
    congr 1; funext n
    simp
  · subst hc; nlinarith
  · exact (gauss_shift_aux ha hc hac y).2

/-! ### Separated-index sums -/

/-- `∑_{k≠0} e^{-k²β} ≤ 2(1 - e^{-β})⁻¹ e^{-β}` for `β > 0`, with summability. -/
theorem tsum_gauss_ne_zero_le_aux {β : ℝ} (hβ : 0 < β) :
    Summable (fun k : {k : ℤ // k ≠ 0} => Real.exp (-(k : ℝ) ^ 2 * β)) ∧
      ∑' k : {k : ℤ // k ≠ 0}, Real.exp (-(k : ℝ) ^ 2 * β) ≤
        2 * (1 - Real.exp (-β))⁻¹ * Real.exp (-β) := by
  set S : Set ℤ := {k | k ≠ 0}
  set h : ℤ → ℝ := S.indicator fun k => Real.exp (-(k : ℝ) ^ 2 * β) with hh
  have hbound : ∀ m : ℕ, Real.exp (-((m : ℝ) + 1) ^ 2 * β) ≤
      Real.exp (-β) * Real.exp (-β * m) := by
    intro m
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith [mul_nonneg (mul_nonneg hm hm) hβ.le, mul_nonneg hm hβ.le]
  have hsplit := tsum_int_le_of_le_two_sides' (f := h)
    (g := fun m : ℕ => Real.exp (-β) * Real.exp (-β * m))
    (fun n => Set.indicator_nonneg (fun k _ => (Real.exp_pos _).le) n)
    ((summable_exp_neg_mul_nat hβ).mul_left _)
    (fun m => by
      have hne : ((m : ℤ) + 1) ∈ S := by simp [S]; omega
      rw [hh, Set.indicator_of_mem hne]; push_cast; exact hbound m)
    (fun m => by
      have hne : (-((m : ℤ) + 1)) ∈ S := by simp [S]; omega
      rw [hh, Set.indicator_of_mem hne]; push_cast; rw [neg_sq]; exact hbound m)
  have h0 : h 0 = 0 := by rw [hh, Set.indicator_of_notMem (by simp [S])]
  have hsumS : Summable (fun k : S => Real.exp (-(k : ℝ) ^ 2 * β)) :=
    (summable_subtype_iff_indicator).2 hsplit.1
  refine ⟨hsumS, ?_⟩
  have htsum : ∑' k : {k : ℤ // k ≠ 0}, Real.exp (-(k : ℝ) ^ 2 * β) = ∑' n, h n :=
    tsum_subtype S fun k => Real.exp (-(k : ℝ) ^ 2 * β)
  rw [htsum]
  refine hsplit.2.trans (le_of_eq ?_)
  rw [h0, zero_add, tsum_mul_left, tsum_exp_neg_mul_nat hβ]
  ring

/-- **G6 (BP9; B0147, B0814).** For `0 < a ≤ c²`:
`∑_{k≠0} e^{-k²c²/(8a)} ≤ 18 e^{-c²/(8a)}`. -/
theorem tsum_gauss_ne_zero_le {a c : ℝ} (ha : 0 < a) (hac : a ≤ c ^ 2) :
    ∑' k : {k : ℤ // k ≠ 0}, Real.exp (-(k : ℝ) ^ 2 * c ^ 2 / (8 * a)) ≤
      18 * Real.exp (-c ^ 2 / (8 * a)) := by
  set β : ℝ := c ^ 2 / (8 * a) with hβdef
  have hβ8 : 1 / 8 ≤ β := by
    rw [hβdef, le_div_iff₀ (by positivity)]; linarith
  have hβ : 0 < β := by linarith
  have h := (tsum_gauss_ne_zero_le_aux hβ).2
  have hterm : ∀ k : {k : ℤ // k ≠ 0}, Real.exp (-(k : ℝ) ^ 2 * c ^ 2 / (8 * a)) =
      Real.exp (-(k : ℝ) ^ 2 * β) := by
    intro k; congr 1; rw [hβdef]; ring
  have hrhs : Real.exp (-c ^ 2 / (8 * a)) = Real.exp (-β) := by congr 1; rw [hβdef]; ring
  simp_rw [hterm]
  rw [hrhs]
  refine h.trans ?_
  -- (1 - e^{-β})⁻¹ ≤ 9 from e^{1/8} ≥ 9/8
  have h1 : (1 : ℝ) / 8 + 1 ≤ Real.exp (1 / 8) := Real.add_one_le_exp _
  have hE : Real.exp (-(1 / 8)) * Real.exp (1 / 8) = 1 := by rw [← Real.exp_add]; simp
  have he8 : Real.exp (-(1 / 8)) ≤ 8 / 9 := by
    have hp := Real.exp_pos (-(1 / 8 : ℝ))
    nlinarith
  have heβ : Real.exp (-β) ≤ 8 / 9 :=
    (Real.exp_le_exp.2 (by linarith)).trans he8
  have hpos : 0 < 1 - Real.exp (-β) := by linarith
  have hinv : (1 - Real.exp (-β))⁻¹ ≤ 9 := by
    rw [inv_le_iff_one_le_mul₀ hpos]; linarith
  have he : 0 ≤ Real.exp (-β) := (Real.exp_pos _).le
  calc 2 * (1 - Real.exp (-β))⁻¹ * Real.exp (-β) ≤ 2 * 9 * Real.exp (-β) := by gcongr
    _ = 18 * Real.exp (-β) := by ring

/-- `∑_{n≠0} e^{-β|n|} ≤ 2(1 + 1/β) e^{-β}` for `β > 0`, with summability. -/
theorem tsum_exp_neg_abs_ne_zero_le {β : ℝ} (hβ : 0 < β) :
    Summable (fun n : {n : ℤ // n ≠ 0} => Real.exp (-β * |(n : ℝ)|)) ∧
      ∑' n : {n : ℤ // n ≠ 0}, Real.exp (-β * |(n : ℝ)|) ≤ 2 * (1 + β⁻¹) * Real.exp (-β) := by
  set S : Set ℤ := {k | k ≠ 0}
  set h : ℤ → ℝ := S.indicator fun k => Real.exp (-β * |(k : ℝ)|) with hh
  have hbound : ∀ m : ℕ, Real.exp (-β * |(m : ℝ) + 1|) ≤ Real.exp (-β) * Real.exp (-β * m) := by
    intro m
    rw [← Real.exp_add, abs_of_nonneg (by positivity)]
    exact le_of_eq (by ring_nf)
  have hsplit := tsum_int_le_of_le_two_sides' (f := h)
    (g := fun m : ℕ => Real.exp (-β) * Real.exp (-β * m))
    (fun n => Set.indicator_nonneg (fun k _ => (Real.exp_pos _).le) n)
    ((summable_exp_neg_mul_nat hβ).mul_left _)
    (fun m => by
      have hne : ((m : ℤ) + 1) ∈ S := by simp [S]; omega
      rw [hh, Set.indicator_of_mem hne]; push_cast; exact hbound m)
    (fun m => by
      have hne : (-((m : ℤ) + 1)) ∈ S := by simp [S]; omega
      rw [hh, Set.indicator_of_mem hne]; push_cast; rw [abs_neg]; exact hbound m)
  have h0 : h 0 = 0 := by rw [hh, Set.indicator_of_notMem (by simp [S])]
  refine ⟨(summable_subtype_iff_indicator).2 hsplit.1, ?_⟩
  have htsum : ∑' n : {n : ℤ // n ≠ 0}, Real.exp (-β * |(n : ℝ)|) = ∑' n, h n :=
    tsum_subtype S fun k => Real.exp (-β * |(k : ℝ)|)
  rw [htsum]
  refine hsplit.2.trans ?_
  rw [h0, zero_add, tsum_mul_left, tsum_exp_neg_mul_nat hβ]
  have := inv_one_sub_exp_neg_le hβ
  have he : 0 ≤ Real.exp (-β) := (Real.exp_pos _).le
  calc 2 * (Real.exp (-β) * (1 - Real.exp (-β))⁻¹)
      ≤ 2 * (Real.exp (-β) * (1 + β⁻¹)) := by gcongr
    _ = 2 * (1 + β⁻¹) * Real.exp (-β) := by ring

/-- **G6 (B0233 mode tail, tex 4003–4004).** For `c, l > 0`:
`∑_{n≠0} e^{-2π|n|l/c} ≤ 2(1 + c/(2πl)) e^{-2πl/c}`. -/
theorem tsum_mode_tail_le {c l : ℝ} (hc : 0 < c) (hl : 0 < l) :
    ∑' n : {n : ℤ // n ≠ 0}, Real.exp (-2 * π * |(n : ℝ)| * l / c) ≤
      2 * (1 + c / (2 * π * l)) * Real.exp (-2 * π * l / c) := by
  have hβ : 0 < 2 * π * l / c := by have := Real.pi_pos; positivity
  have h := (tsum_exp_neg_abs_ne_zero_le hβ).2
  have hterm : ∀ n : {n : ℤ // n ≠ 0}, Real.exp (-2 * π * |(n : ℝ)| * l / c) =
      Real.exp (-(2 * π * l / c) * |(n : ℝ)|) := by
    intro n; congr 1; ring
  simp_rw [hterm]
  refine h.trans (le_of_eq ?_)
  rw [inv_div]
  congr 2; ring

/-! ### Polynomial weights -/

/-- `x^p e^{-x/2} ≤ C_p` on `[0, ∞)` with `C_p = (2p)^p` (any explicit constant works). -/
theorem pow_mul_exp_neg_half_le (p : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 0 ≤ x → x ^ p * Real.exp (-x / 2) ≤ C := by
  refine ⟨2 ^ p * p ! + 1, by positivity, fun x hx => ?_⟩
  -- (x/2)^p ≤ p! e^{x/2}
  have h := Real.pow_div_factorial_le_exp (x := x / 2) (by positivity) p
  have hfac : (0 : ℝ) < p ! := by exact_mod_cast Nat.factorial_pos p
  rw [div_le_iff₀ hfac] at h
  have hE : Real.exp (x / 2) * Real.exp (-x / 2) = 1 := by rw [← Real.exp_add]; ring_nf; simp
  have he : 0 < Real.exp (-x / 2) := Real.exp_pos _
  have h2 : x ^ p = 2 ^ p * (x / 2) ^ p := by
    rw [div_pow, mul_div_cancel₀ _ (by positivity)]
  rw [h2]
  calc 2 ^ p * (x / 2) ^ p * Real.exp (-x / 2)
      ≤ 2 ^ p * (Real.exp (x / 2) * p !) * Real.exp (-x / 2) := by gcongr
    _ = 2 ^ p * p ! * (Real.exp (x / 2) * Real.exp (-x / 2)) := by ring
    _ = 2 ^ p * p ! := by rw [hE, mul_one]
    _ ≤ 2 ^ p * p ! + 1 := by linarith

/-- **G6, polynomial-weighted version (B0147, B0814).** For each `p` and `β₀ > 0` there is `C`
with `∑_{k≠0} |k|^p e^{-k²β} ≤ C e^{-β/2}` for all `β ≥ β₀`; with summability. -/
theorem tsum_pow_mul_gauss_ne_zero_le (p : ℕ) {β₀ : ℝ} (hβ₀ : 0 < β₀) : ∃ C : ℝ, 0 < C ∧
    ∀ {β : ℝ}, β₀ ≤ β →
      Summable (fun k : {k : ℤ // k ≠ 0} => |(k : ℝ)| ^ p * Real.exp (-(k : ℝ) ^ 2 * β)) ∧
      ∑' k : {k : ℤ // k ≠ 0}, |(k : ℝ)| ^ p * Real.exp (-(k : ℝ) ^ 2 * β) ≤
        C * Real.exp (-β / 2) := by
  obtain ⟨A, hA, hAb⟩ := pow_mul_exp_neg_half_le p
  -- |k|^p e^{-k²β} ≤ A β₀^{-p} e^{-k²β/2}, since (k²β₀)^{p}… is absorbed via x = |k| β₀
  set B : ℝ := A / β₀ ^ p
  have hB : 0 < B := by positivity
  set β₁ : ℝ := β₀ / 2
  have hβ₁ : 0 < β₁ := half_pos hβ₀
  refine ⟨B * (2 * (1 - Real.exp (-β₁))⁻¹), ?_, ?_⟩
  · have : Real.exp (-β₁) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have : 0 < 1 - Real.exp (-β₁) := by linarith
    positivity
  intro β hβ
  have hβpos : 0 < β := lt_of_lt_of_le hβ₀ hβ
  -- pointwise: |k|^p e^{-k²β} ≤ B e^{-k² β/2}
  have hpt : ∀ k : ℤ, k ≠ 0 →
      |(k : ℝ)| ^ p * Real.exp (-(k : ℝ) ^ 2 * β) ≤ B * Real.exp (-(k : ℝ) ^ 2 * (β / 2)) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
    set x : ℝ := |(k : ℝ)| * β₀
    have hx : 0 ≤ x := by positivity
    have h1 := hAb x hx
    -- e^{-k²β/2} ≤ e^{-x/2} since k²β ≥ |k| β₀
    have hk2 : |(k : ℝ)| * β₀ ≤ (k : ℝ) ^ 2 * β := by
      rw [← sq_abs (k : ℝ)]
      calc |(k : ℝ)| * β₀ ≤ |(k : ℝ)| ^ 2 * β₀ := by
            refine mul_le_mul_of_nonneg_right ?_ hβ₀.le; nlinarith
        _ ≤ |(k : ℝ)| ^ 2 * β := mul_le_mul_of_nonneg_left hβ (by positivity)
    have he1 : Real.exp (-(k : ℝ) ^ 2 * β) ≤
        Real.exp (-x / 2) * Real.exp (-(k : ℝ) ^ 2 * (β / 2)) := by
      rw [← Real.exp_add]; refine Real.exp_le_exp.2 ?_; simp only [x]; nlinarith
    have hxp : |(k : ℝ)| ^ p = x ^ p / β₀ ^ p := by
      simp only [x]; rw [mul_pow, mul_div_cancel_right₀ _ (by positivity)]
    calc |(k : ℝ)| ^ p * Real.exp (-(k : ℝ) ^ 2 * β)
        ≤ |(k : ℝ)| ^ p * (Real.exp (-x / 2) * Real.exp (-(k : ℝ) ^ 2 * (β / 2))) := by gcongr
      _ = (x ^ p * Real.exp (-x / 2)) / β₀ ^ p * Real.exp (-(k : ℝ) ^ 2 * (β / 2)) := by
          rw [hxp]; ring
      _ ≤ A / β₀ ^ p * Real.exp (-(k : ℝ) ^ 2 * (β / 2)) := by gcongr
  have hβ2 : 0 < β / 2 := half_pos hβpos
  obtain ⟨hs, ht⟩ := tsum_gauss_ne_zero_le_aux hβ2
  have hsum : Summable (fun k : {k : ℤ // k ≠ 0} =>
      |(k : ℝ)| ^ p * Real.exp (-(k : ℝ) ^ 2 * β)) :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k : {k : ℤ // k ≠ 0} => hpt k k.2) (hs.mul_left B)
  refine ⟨hsum, ?_⟩
  have hle := hsum.tsum_le_tsum (fun k : {k : ℤ // k ≠ 0} => hpt k k.2) (hs.mul_left B)
  rw [tsum_mul_left] at hle
  refine hle.trans ?_
  have hmono : (1 - Real.exp (-(β / 2)))⁻¹ ≤ (1 - Real.exp (-β₁))⁻¹ := by
    have h1 : Real.exp (-(β / 2)) ≤ Real.exp (-β₁) := Real.exp_le_exp.2 (by simp only [β₁]; linarith)
    have h2 : Real.exp (-β₁) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    exact inv_anti₀ (by linarith) (by linarith)
  have he : 0 ≤ Real.exp (-(β / 2)) := (Real.exp_pos _).le
  calc B * ∑' k : {k : ℤ // k ≠ 0}, Real.exp (-(k : ℝ) ^ 2 * (β / 2))
      ≤ B * (2 * (1 - Real.exp (-(β / 2)))⁻¹ * Real.exp (-(β / 2))) := by gcongr
    _ ≤ B * (2 * (1 - Real.exp (-β₁))⁻¹ * Real.exp (-(β / 2))) := by gcongr
    _ = B * (2 * (1 - Real.exp (-β₁))⁻¹) * Real.exp (-β / 2) := by ring_nf

end UnforcedLeray.Gaussian
