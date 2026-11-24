import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff

/-!
# Sanity lemmas for the affine norm functional (source lines 4741-4752)

Nonnegativity of `affNorm` and vanishing of `affNorm as 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Real
open scoped BigOperators

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The zero matrix function has all `(s∂_s)^j` derivatives zero. -/
lemma sDerivIter_zero_fn (j : ℕ) : sDerivIter j (0 : ℝ → Mat3) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext s
    have hd : deriv (0 : ℝ → Mat3) s = 0 := by
      simp
    simp [sDerivIter, sDeriv, ih, hd]

/-- Frobenius norm is nonnegative. -/
lemma frob_nonneg (A : Mat3) : 0 ≤ frob A := Real.sqrt_nonneg _

/-- The weighted integrand is nonnegative for `as` arbitrary and `s > 0`. -/
lemma affTerm_nonneg (as : ℝ) (k : ℕ) (A : ℝ → Mat3) (s : ℝ) (hs : 0 < s) :
    0 ≤ affTerm as k A s := by
  unfold affTerm affSum
  apply mul_nonneg
  · apply mul_nonneg (Real.exp_nonneg _)
    exact Real.rpow_nonneg hs.le _
  · exact Finset.sum_nonneg (fun j _ => frob_nonneg _)

/-- The affine norm is nonnegative. -/
theorem affNorm_nonneg (as : ℝ) (A : ℝ → Mat3) (h : IsAffElem as A) : 0 ≤ affNorm as A := by
  unfold affNorm
  apply Real.sSup_nonneg
  rintro x ⟨s, hs, rfl⟩
  exact affTerm_nonneg as 6 A s hs

/-- The affine norm of the zero function vanishes. -/
theorem affNorm_zero (as : ℝ) : affNorm as 0 = 0 := by
  have hterm : ∀ s : ℝ, affTerm as 6 (0 : ℝ → Mat3) s = 0 := by
    intro s
    have hsum : affSum 6 (0 : ℝ → Mat3) s = 0 := by
      unfold affSum
      apply Finset.sum_eq_zero
      intro j _
      have hz : sDerivIter j (0 : ℝ → Mat3) s = 0 := by
        rw [sDerivIter_zero_fn j]
        rfl
      rw [hz]
      simp [frob]
    unfold affTerm
    rw [hsum, mul_zero]
  have himg : affTerm as 6 (0 : ℝ → Mat3) '' Ioi 0 = {0} := by
    ext x
    constructor
    · rintro ⟨s, _, rfl⟩
      simp [hterm s]
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨1, by norm_num, hterm 1⟩
  unfold affNorm
  rw [himg, csSup_singleton]

end UnforcedLeray.Short.PartIIIb.Concrete
