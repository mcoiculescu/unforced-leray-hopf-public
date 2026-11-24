import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Leaf `PartIII-b:C/env/2`: Leibniz rule for `s∂_s` on `(0,∞)`

Source of record: `the November 2 reference manuscript` (73 pages), lines
4955-4962 (`A^y = χ_f A`, and `(s∂_s)^j A^y` in terms of `(s∂_s)^k A`).  The statement
`SDerivIterLeibniz` is defined in `Concrete/AffineEnvelope.lean`; this file proves it.

Proof: induction on `j`.  The step uses `s∂_s B = s • deriv B s`, the product rule for the
scalar function `F i = (s∂_s)^i f` and the matrix function `G k = (s∂_s)^k A`, and Pascal's
rule for `Finset.sum_antidiagonal_choose_succ_nsmul`, together with the symmetry
`C(j, i) = C(j, j - i)` on the antidiagonal.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `C/env/2`: the Leibniz rule for `s∂_s` on `(0,∞)`. -/
theorem sDerivIterLeibniz : SDerivIterLeibniz := by
  unfold SDerivIterLeibniz
  intro f A j
  induction j with
  | zero =>
    intro _ _ s _
    simp [sDerivIter, sDerivIterR]
  | succ j ih =>
    intro hf hA s hs
    have hs0 : (0 : ℝ) < s := hs
    -- the induction hypothesis on `(0,∞)`, as an eventual equality at `s`
    have hIH : sDerivIter j (fun t => f t • A t) =ᶠ[nhds s]
        (fun t => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j,
          j.choose ij.1 • (sDerivIterR ij.1 f t • sDerivIter ij.2 A t)) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds hs0) (ih hf (fun k hk => hA k (by omega)))
    have hFd : ∀ i, HasDerivAt (sDerivIterR i f) (deriv (sDerivIterR i f) s) s :=
      fun i => ((hf i) s).hasDerivAt
    have hGd : ∀ k, k ≤ j → HasDerivAt (sDerivIter k A) (deriv (sDerivIter k A) s) s :=
      fun k hk => ((hA k (by omega)).differentiableAt (Ioi_mem_nhds hs0)).hasDerivAt
    -- derivative of each term of the sum
    have hterm : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal j,
        HasDerivAt (fun t => j.choose ij.1 • (sDerivIterR ij.1 f t • sDerivIter ij.2 A t))
          (j.choose ij.1 • (sDerivIterR ij.1 f s • deriv (sDerivIter ij.2 A) s +
            deriv (sDerivIterR ij.1 f) s • sDerivIter ij.2 A s)) s := by
      intro ij hij
      have hle : ij.2 ≤ j := by
        have := Finset.HasAntidiagonal.mem_antidiagonal.1 hij
        omega
      exact HasDerivAt.const_smul (j.choose ij.1) ((hFd ij.1).smul (hGd ij.2 hle))
    have hsum : HasDerivAt (fun t => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j,
          j.choose ij.1 • (sDerivIterR ij.1 f t • sDerivIter ij.2 A t))
        (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, j.choose ij.1 •
          (sDerivIterR ij.1 f s • deriv (sDerivIter ij.2 A) s +
            deriv (sDerivIterR ij.1 f) s • sDerivIter ij.2 A s)) s :=
      HasDerivAt.fun_sum hterm
    -- Pascal's rule, with the terms written out
    have hpas := Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i k => sDerivIterR i f s • sDerivIter k A s) j
    -- the product rule, term by term
    have step1 : ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, s • (j.choose ij.1 •
          (sDerivIterR ij.1 f s • deriv (sDerivIter ij.2 A) s +
            deriv (sDerivIterR ij.1 f) s • sDerivIter ij.2 A s))
        = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, j.choose ij.1 •
            (sDerivIterR ij.1 f s • sDerivIter (ij.2 + 1) A s)
          + ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, j.choose ij.1 •
            (sDerivIterR (ij.1 + 1) f s • sDerivIter ij.2 A s) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ij _
      simp only [sDerivIter, sDeriv, sDerivIterR, sDerivR, ← Nat.cast_smul_eq_nsmul ℝ]
      module
    -- Pascal's rule uses `C(j, ij.2)`; replace it by `C(j, ij.1)` on the antidiagonal
    have step2 : ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, j.choose ij.1 •
            (sDerivIterR (ij.1 + 1) f s • sDerivIter ij.2 A s)
        = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, j.choose ij.2 •
            (sDerivIterR (ij.1 + 1) f s • sDerivIter ij.2 A s) := by
      apply Finset.sum_congr rfl
      intro ij hij
      have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hij
      rw [Nat.choose_symm_of_eq_add (show j = ij.2 + ij.1 by omega)]
    change s • deriv (sDerivIter j (fun t => f t • A t)) s = _
    rw [hIH.deriv_eq, hsum.deriv, Finset.smul_sum, step1, step2]
    exact hpas.symm

end UnforcedLeray.Short.PartIIIb.Concrete
