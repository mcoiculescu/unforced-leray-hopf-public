import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Extending a two-parameter family from a strip of unit width

Let `F : ℝ → ℝ → M` take values in a monoid and satisfy the *local evolution law*
`F τ r * F r s = F τ s` whenever `s ≤ r ≤ τ ≤ s + 1`.  Iterating unit strips,

`extend F τ s = F τ (s + n) * F (s + n) (s + n - 1) * ⋯ * F (s + 1) s`,  `n = ⌊τ - s⌋₊`,

defines a family that agrees with `F` on the strip and satisfies the evolution law for all
`s ≤ r ≤ τ`.  In a seminormed ring a uniform bound `‖F τ s‖ ≤ C` on the strip gives the
exponential bound `‖extend F τ s‖ ≤ C e^{(log C)(τ - s)}`, and a jointly periodic `F` has a
jointly periodic extension.  This is the "iteration of the strip" step of `paper/main.tex`,
lines 300-306; it is purely algebraic.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Infra.VolterraEvolution.Cocycle

section Monoid

variable {M : Type*} [Monoid M] (F : ℝ → ℝ → M)

/-- The local evolution law on the strip `s ≤ r ≤ τ ≤ s + 1` (degenerate cases included). -/
def LocalLaw : Prop :=
  ∀ s r τ : ℝ, s ≤ r → r ≤ τ → τ ≤ s + 1 → F τ r * F r s = F τ s

/-- The product of `n` unit steps starting at `s`:
`steps F n s = F (s + n) (s + n - 1) * ⋯ * F (s + 1) s`. -/
def steps : ℕ → ℝ → M
  | 0 => fun _ => 1
  | n + 1 => fun s => F (s + ((n : ℝ) + 1)) (s + n) * steps n s

/-- The extension of `F` to all elapsed times by iterating unit strips. -/
def extend (τ s : ℝ) : M :=
  F τ (s + (⌊τ - s⌋₊ : ℝ)) * steps F ⌊τ - s⌋₊ s

@[simp] theorem steps_zero (s : ℝ) : steps F 0 s = 1 := rfl

theorem steps_succ (n : ℕ) (s : ℝ) :
    steps F (n + 1) s = F (s + ((n : ℝ) + 1)) (s + n) * steps F n s := rfl

variable {F}

/-- Moving the base point inside one strip shifts a unit step. -/
theorem shift_step (hF : LocalLaw F) {s r : ℝ} (hsr : s ≤ r) (hrs : r ≤ s + 1) :
    F (r + 1) r * F r s = F (r + 1) (s + 1) * F (s + 1) s := by
  have h1 : F (r + 1) (s + 1) * F (s + 1) r = F (r + 1) r :=
    hF r (s + 1) (r + 1) hrs (by linarith) le_rfl
  have h2 : F (s + 1) r * F r s = F (s + 1) s := hF s r (s + 1) hsr hrs le_rfl
  rw [← h1, mul_assoc, h2]

theorem steps_mul (hF : LocalLaw F) (n : ℕ) {s r : ℝ} (hsr : s ≤ r) (hrs : r ≤ s + 1) :
    steps F n r * F r s = F (r + n) (s + n) * steps F n s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [steps_succ, steps_succ, mul_assoc, ih, ← mul_assoc, ← mul_assoc]
    congr 1
    have := shift_step hF (s := s + n) (r := r + n) (by linarith) (by linarith)
    simpa only [Nat.cast_succ, add_assoc] using this

/-- On every closed unit cell `[s + n, s + n + 1]` the extension is a product of steps. -/
theorem extend_eq (hF : LocalLaw F) (n : ℕ) {s τ : ℝ} (h1 : s + n ≤ τ) (h2 : τ ≤ s + n + 1) :
    extend F τ s = F τ (s + n) * steps F n s := by
  have hn : n ≤ ⌊τ - s⌋₊ := Nat.le_floor (by linarith)
  have hn' : ⌊τ - s⌋₊ ≤ n + 1 := by
    apply Nat.floor_le_of_le
    push_cast
    linarith
  rcases Nat.eq_or_lt_of_le hn with h | h
  · rw [extend, ← h]
  · have hm : ⌊τ - s⌋₊ = n + 1 := by omega
    have hτ : τ = s + n + 1 := by
      have : ((n + 1 : ℕ) : ℝ) ≤ τ - s := by
        rw [← hm]; exact Nat.floor_le (by linarith)
      push_cast at this
      linarith
    rw [extend, hm, steps_succ, ← mul_assoc]
    congr 1
    have e : s + (((n + 1 : ℕ) : ℝ)) = τ := by push_cast; linarith
    have e' : s + ((n : ℝ) + 1) = τ := by linarith
    rw [e, e']
    exact hF (s + n) τ τ (by linarith) le_rfl (by linarith)

/-- The extension agrees with `F` on the strip `s ≤ τ ≤ s + 1`. -/
theorem extend_eq_self (hF : LocalLaw F) {s τ : ℝ} (h1 : s ≤ τ) (h2 : τ ≤ s + 1) :
    extend F τ s = F τ s := by
  have := extend_eq hF 0 (s := s) (τ := τ) (by simpa using h1) (by simpa using h2)
  simpa using this

/-- Peeling off one strip at the start. -/
theorem extend_mul_of_le_one (hF : LocalLaw F) {s r τ : ℝ} (hsr : s ≤ r) (hrs : r ≤ s + 1)
    (hrτ : r ≤ τ) : extend F τ r * F r s = extend F τ s := by
  set n := ⌊τ - r⌋₊ with hn
  have hlo : (n : ℝ) ≤ τ - r := Nat.floor_le (by linarith)
  have hhi : τ - r < n + 1 := Nat.lt_floor_add_one _
  have hext : extend F τ r = F τ (r + n) * steps F n r := extend_eq hF n (by linarith) (by linarith)
  rw [hext, mul_assoc, steps_mul hF n hsr hrs, ← mul_assoc]
  by_cases hτ : τ ≤ s + n + 1
  · rw [hF (s + n) (r + n) τ (by linarith) (by linarith) hτ]
    exact (extend_eq hF n (by linarith) hτ).symm
  · rw [not_le] at hτ
    have e1 : F τ (s + n + 1) * F (s + n + 1) (r + n) = F τ (r + n) :=
      hF (r + n) (s + n + 1) τ (by linarith) hτ.le (by linarith)
    have e2 : F (s + n + 1) (r + n) * F (r + n) (s + n) = F (s + n + 1) (s + n) :=
      hF (s + n) (r + n) (s + n + 1) (by linarith) (by linarith) le_rfl
    rw [← e1, mul_assoc, mul_assoc, ← mul_assoc (F (s + n + 1) (r + n)), e2]
    have := extend_eq hF (n + 1) (s := s) (τ := τ) (by push_cast; linarith)
      (by push_cast; linarith)
    rw [this, steps_succ]
    push_cast
    rw [show s + ((n : ℝ) + 1) = s + n + 1 by ring]

/-- The global evolution law for the extension: `extend τ r * extend r s = extend τ s`
for all `s ≤ r ≤ τ`. -/
theorem extend_mul (hF : LocalLaw F) {s r τ : ℝ} (hsr : s ≤ r) (hrτ : r ≤ τ) :
    extend F τ r * extend F r s = extend F τ s := by
  suffices H : ∀ n : ℕ, ∀ s : ℝ, s ≤ r → r ≤ s + n + 1 →
      extend F τ r * extend F r s = extend F τ s by
    exact H ⌊r - s⌋₊ s hsr (by have := Nat.lt_floor_add_one (r - s); linarith)
  intro n
  induction n with
  | zero =>
    intro s h1 h2
    have h2' : r ≤ s + 1 := by simpa using h2
    rw [extend_eq_self hF h1 h2']
    exact extend_mul_of_le_one hF h1 h2' hrτ
  | succ n ih =>
    intro s h1 h2
    by_cases h : r ≤ s + 1
    · rw [extend_eq_self hF h1 h]
      exact extend_mul_of_le_one hF h1 h hrτ
    · rw [not_le] at h
      have hsplit : extend F r (s + 1) * F (s + 1) s = extend F r s :=
        extend_mul_of_le_one hF (by linarith) le_rfl h.le
      rw [← hsplit, ← mul_assoc, ih (s + 1) h.le (by push_cast at h2; linarith)]
      exact extend_mul_of_le_one hF (by linarith) le_rfl (by linarith)

/-- Joint periodicity is inherited by the extension. -/
theorem extend_periodic {T : ℝ} (hper : ∀ τ s, F (τ + T) (s + T) = F τ s) (τ s : ℝ) :
    extend F (τ + T) (s + T) = extend F τ s := by
  have hsteps : ∀ n : ℕ, ∀ s : ℝ, steps F n (s + T) = steps F n s := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [steps_succ, steps_succ, ih]
      congr 1
      rw [show s + T + ((n : ℝ) + 1) = s + ((n : ℝ) + 1) + T by ring,
        show s + T + (n : ℝ) = s + n + T by ring, hper]
  rw [extend, extend, add_sub_add_right_eq_sub, hsteps,
    show s + T + (⌊τ - s⌋₊ : ℝ) = s + ⌊τ - s⌋₊ + T by ring, hper]

end Monoid

section Norm

variable {M : Type*} [SeminormedRing M] {F : ℝ → ℝ → M}

theorem norm_steps_le {C : ℝ} (hC : ∀ s τ : ℝ, s ≤ τ → τ ≤ s + 1 → ‖F τ s‖ ≤ C)
    (h1 : ‖(1 : M)‖ ≤ 1) (n : ℕ) (s : ℝ) : ‖steps F n s‖ ≤ C ^ n := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 0 le_rfl (by norm_num))
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    rw [steps_succ, pow_succ']
    refine (norm_mul_le _ _).trans (mul_le_mul (hC _ _ (by linarith) (by linarith)) ih
      (norm_nonneg _) hC0)

/-- Power bound for the extension: `‖extend F τ s‖ ≤ C ^ (⌊τ - s⌋₊ + 1)`. -/
theorem norm_extend_le_pow {C : ℝ} (hC : ∀ s τ : ℝ, s ≤ τ → τ ≤ s + 1 → ‖F τ s‖ ≤ C)
    (h1 : ‖(1 : M)‖ ≤ 1) {s τ : ℝ} (hsτ : s ≤ τ) :
    ‖extend F τ s‖ ≤ C ^ (⌊τ - s⌋₊ + 1) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 0 le_rfl (by norm_num))
  have hlo : (⌊τ - s⌋₊ : ℝ) ≤ τ - s := Nat.floor_le (by linarith)
  have hhi : τ - s < ⌊τ - s⌋₊ + 1 := Nat.lt_floor_add_one _
  rw [extend, pow_succ']
  exact (norm_mul_le _ _).trans (mul_le_mul (hC _ _ (by linarith) (by linarith))
    (norm_steps_le hC h1 _ _) (norm_nonneg _) hC0)

/-- Exponential bound for the extension: `‖extend F τ s‖ ≤ C e^{(log C)(τ - s)}` when `C ≥ 1`. -/
theorem norm_extend_le_exp {C : ℝ} (hC1 : 1 ≤ C)
    (hC : ∀ s τ : ℝ, s ≤ τ → τ ≤ s + 1 → ‖F τ s‖ ≤ C)
    (h1 : ‖(1 : M)‖ ≤ 1) {s τ : ℝ} (hsτ : s ≤ τ) :
    ‖extend F τ s‖ ≤ C * Real.exp (Real.log C * (τ - s)) := by
  refine (norm_extend_le_pow hC h1 hsτ).trans ?_
  have hC0 : 0 < C := by linarith
  have hlo : (⌊τ - s⌋₊ : ℝ) ≤ τ - s := Nat.floor_le (by linarith)
  rw [pow_succ']
  refine mul_le_mul_of_nonneg_left ?_ hC0.le
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hC0]
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hlo (Real.log_nonneg hC1))

end Norm

end UnforcedLeray.Infra.VolterraEvolution.Cocycle
