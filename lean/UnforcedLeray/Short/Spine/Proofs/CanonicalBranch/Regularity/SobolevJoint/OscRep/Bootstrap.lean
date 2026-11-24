import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4_1
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep.DerivRep
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep.CoeffBounds

/-!
# Leaf B9 (`OscBootstrap`): bounds for all derivatives from those of `φ, φ'`

Proves `UnforcedLeray.Short.Spine.OscBootstrap` (`Sub/SP_CAN4_4_1.lean`), exactly as stated.

Source of record: `the November 2 reference manuscript`, lines 1134-1140.

Method. Fix `0 < a < b`. Write `BndOf a b C j` for the bound of order `j` with constant `C`
(the conclusion of `OscBootstrap` at order `j`, with `C` fixed in advance). Induction on `m`
proves `Q m`: there is `C ≥ 0` with `BndOf a b C j` for every `j ≤ m + 1`, one common constant.

* `Q 0`: `C = 1`. Orders `0` and `1` are the hypotheses (`(1+n) ≤ (1+n)^2`).
* `Q m → Q (m+1)`: `OscDerivRep` writes `φ^{(m+2)}(r)` as a sum over `i ≤ m` of
  `C(m,i) (c₁^{(i)}(r) φ^{(m-i+1)}(r) + c₀^{(i)}(r) φ^{(m-i)}(r))`. The coefficient bounds
  `|c₁^{(i)}|, |c₀^{(i)}| ≤ D_i (1+n)` on `[a, b]` come from `OscCoeffBounds`. Every
  `φ^{(j)}`, `j ≤ m+1`, is at most `C M (1+n)^{m+2}` by `Q m` and `1+n ≥ 1`. Hence the
  `i`-th term is at most `C(m,i) · 2 C D_i · M (1+n)^{m+3}`, and the sum is at most
  `K M (1+n)^{m+3}` with `K = ∑_i C(m,i) 2 C D_i`. The new constant is `max C K`.

The statement for order `m` then follows from `Q m`.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Polynomial
open scoped ContDiff Topology InnerProductSpace

open UnforcedLeray.Short.Spine

namespace OscBootstrapAux

/-- The conclusion of `OscBootstrap` at order `j` with constant `C`, on `[a, b]`. -/
def BndOf (a b : ℝ) (C : ℝ) (j : ℕ) : Prop :=
  ∀ (n : ℕ) (φ : ℝ → ℂ) (M : ℝ), 0 ≤ M → OscOde n φ →
    (∀ r ∈ Icc a b, ‖φ r‖ ≤ M * (1 + (n : ℝ)) ∧ ‖deriv φ r‖ ≤ M * (1 + (n : ℝ))) →
      ∀ r ∈ Icc a b, ‖iteratedDeriv j φ r‖ ≤ C * M * (1 + (n : ℝ)) ^ (j + 1)

/-- The bound is monotone in the constant. -/
lemma bndOf_mono {a b C C' : ℝ} {j : ℕ} (hCC : C ≤ C') (h : BndOf a b C j) :
    BndOf a b C' j := by
  intro n φ M hM hφ hyp r hr
  refine (h n φ M hM hφ hyp r hr).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hM) (by positivity)

/-- Order `0`: the hypothesis on `φ`, with constant `1`. -/
lemma bndOf_zero (a b : ℝ) : BndOf a b 1 0 := by
  intro n φ M hM hφ hyp r hr
  rw [iteratedDeriv_zero]
  calc ‖φ r‖ ≤ M * (1 + (n : ℝ)) := (hyp r hr).1
    _ = 1 * M * (1 + (n : ℝ)) ^ (0 + 1) := by ring

/-- Order `1`: the hypothesis on `φ'`, with constant `1`. -/
lemma bndOf_one (a b : ℝ) : BndOf a b 1 1 := by
  intro n φ M hM hφ hyp r hr
  rw [iteratedDeriv_one]
  have hn1 : (1 : ℝ) ≤ 1 + (n : ℝ) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : (1 + (n : ℝ)) ≤ (1 + (n : ℝ)) ^ (1 + 1) := by
    rw [pow_succ, pow_one]
    nlinarith [sq_nonneg (n : ℝ), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc ‖deriv φ r‖ ≤ M * (1 + (n : ℝ)) := (hyp r hr).2
    _ ≤ M * (1 + (n : ℝ)) ^ (1 + 1) := mul_le_mul_of_nonneg_left h2 hM
    _ = 1 * M * (1 + (n : ℝ)) ^ (1 + 1) := by ring

/-- The step: from the bounds of orders `≤ m + 1` (constant `C ≥ 0`) to the bound of order
`m + 2` with constant `K = ∑_{i ≤ m} C(m,i) · 2 C D_i`, where `D_i` bounds the coefficient
derivatives `c₁^{(i)}`, `c₀^{(i)}` on `[a, b]`. -/
lemma bootKey {a b : ℝ} (ha : 0 < a) (hab : a < b) (D : ℕ → ℝ)
    (hD : ∀ (i n : ℕ) (r : ℝ), r ∈ Icc a b →
      ‖iteratedDeriv i oscC1 r‖ ≤ D i ∧ ‖iteratedDeriv i (oscC0 n) r‖ ≤ D i * (1 + (n : ℝ)))
    (m : ℕ) (C : ℝ) (hC0 : 0 ≤ C) (hCb : ∀ j ≤ m + 1, BndOf a b C j) :
    ∀ (n : ℕ) (φ : ℝ → ℂ) (M : ℝ), 0 ≤ M → OscOde n φ →
      (∀ r ∈ Icc a b, ‖φ r‖ ≤ M * (1 + (n : ℝ)) ∧ ‖deriv φ r‖ ≤ M * (1 + (n : ℝ))) →
      ∀ r ∈ Icc a b, ‖iteratedDeriv (m + 2) φ r‖ ≤
        (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (2 * C * D i)) * M *
          (1 + (n : ℝ)) ^ (m + 2 + 1) := by
  intro n φ M hM hφ hyp r hr
  have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
  have hrep := oscDerivRep_proof n φ hφ m r hr0
  have hDnn : ∀ i, 0 ≤ D i := fun i => (norm_nonneg _).trans ((hD i 0 a ⟨le_rfl, hab.le⟩).1)
  have hn1 : (1 : ℝ) ≤ 1 + (n : ℝ) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  -- every derivative of order `≤ m + 1` is at most `C M (1+n)^{m+2}` at `r`
  have hlow : ∀ j ≤ m + 1, ‖iteratedDeriv j φ r‖ ≤ C * M * (1 + (n : ℝ)) ^ (m + 2) := by
    intro j hj
    refine (hCb j hj n φ M hM hφ hyp r hr).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by omega)) (mul_nonneg hC0 hM)
  -- each Leibniz term
  have hterm : ∀ i ∈ Finset.range (m + 1),
      ‖(m.choose i : ℂ) * (iteratedDeriv i oscC1 r * iteratedDeriv (m - i + 1) φ r +
          iteratedDeriv i (oscC0 n) r * iteratedDeriv (m - i) φ r)‖ ≤
        ((m.choose i : ℝ) * (2 * C * D i)) * (M * (1 + (n : ℝ)) ^ (m + 2 + 1)) := by
    intro i hi
    have hi' : i ≤ m := by
      have := Finset.mem_range.mp hi
      omega
    obtain ⟨h1, h0⟩ := hD i n r hr
    have hX : 0 ≤ D i * (1 + (n : ℝ)) := mul_nonneg (hDnn i) (by positivity)
    have h1' : ‖iteratedDeriv i oscC1 r‖ ≤ D i * (1 + (n : ℝ)) :=
      h1.trans (le_mul_of_one_le_right (hDnn i) hn1)
    have hA : ‖iteratedDeriv i oscC1 r * iteratedDeriv (m - i + 1) φ r‖ ≤
        (D i * (1 + (n : ℝ))) * (C * M * (1 + (n : ℝ)) ^ (m + 2)) := by
      rw [norm_mul]
      exact mul_le_mul h1' (hlow (m - i + 1) (by omega)) (norm_nonneg _) hX
    have hB : ‖iteratedDeriv i (oscC0 n) r * iteratedDeriv (m - i) φ r‖ ≤
        (D i * (1 + (n : ℝ))) * (C * M * (1 + (n : ℝ)) ^ (m + 2)) := by
      rw [norm_mul]
      exact mul_le_mul h0 (hlow (m - i) (by omega)) (norm_nonneg _) hX
    have hsum := (norm_add_le _ _).trans (add_le_add hA hB)
    rw [norm_mul, Complex.norm_natCast]
    calc (m.choose i : ℝ) * ‖iteratedDeriv i oscC1 r * iteratedDeriv (m - i + 1) φ r +
          iteratedDeriv i (oscC0 n) r * iteratedDeriv (m - i) φ r‖
        ≤ (m.choose i : ℝ) * (2 * (D i * (1 + (n : ℝ))) * (C * M * (1 + (n : ℝ)) ^ (m + 2))) :=
          mul_le_mul_of_nonneg_left (hsum.trans (le_of_eq (by ring))) (Nat.cast_nonneg _)
      _ = ((m.choose i : ℝ) * (2 * C * D i)) * (M * (1 + (n : ℝ)) ^ (m + 2 + 1)) := by ring
  rw [hrep]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans (le_of_eq ?_))
  rw [← Finset.sum_mul]
  ring

/-- `Q m`: one constant `C ≥ 0` serves all orders `j ≤ m + 1`. -/
lemma bootQ {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ m + 1, BndOf a b C j := by
  choose D hD using fun i => oscCoeffBounds_proof a b ha hab i
  intro m
  induction m with
  | zero =>
    refine ⟨1, zero_le_one, fun j hj => ?_⟩
    have hj01 : j = 0 ∨ j = 1 := by omega
    rcases hj01 with rfl | rfl
    · exact bndOf_zero a b
    · exact bndOf_one a b
  | succ m ih =>
    obtain ⟨C, hC0, hCb⟩ := ih
    refine ⟨max C (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (2 * C * D i)),
      le_max_of_le_left hC0, fun j hj => ?_⟩
    rcases (show j ≤ m + 1 ∨ j = m + 2 by omega) with h | rfl
    · exact bndOf_mono (le_max_left _ _) (hCb j h)
    · intro n φ M hM hφ hyp r hr
      exact (bootKey ha hab D hD m C hC0 hCb n φ M hM hφ hyp r hr).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hM)
          (by positivity))

end OscBootstrapAux

/-- **Leaf B9.** For `0 < a < b` and each `m` there is `C` such that every solution `φ` with
`|φ|, |φ'| ≤ M (1+n)` on `[a, b]` satisfies `|φ^{(m)}| ≤ C M (1+n)^{m+1}` on `[a, b]`. -/
theorem oscBootstrap_proof : UnforcedLeray.Short.Spine.OscBootstrap := by
  intro a b ha hab m
  obtain ⟨C, _, hC⟩ := OscBootstrapAux.bootQ ha hab m
  exact ⟨C, fun n φ M hM hφ hyp r hr => hC m (by omega) n φ M hM hφ hyp r hr⟩

end
