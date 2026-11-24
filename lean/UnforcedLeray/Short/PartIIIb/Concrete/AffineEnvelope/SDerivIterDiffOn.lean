import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Leaf `PartIII-b:C/env/1`: `(s∂_s)^k A` is differentiable on `(0,∞)` for `k < 6`

Source of record: `the November 2 reference manuscript` (73 pages), lines
4741-4745 (`A ∈ 𝒜` is `C^6` on `(0,∞)`).  The statement `SDerivIterDiffOn` is defined in
`Concrete/AffineEnvelope.lean`; this file proves it.

Proof: `s∂_s B = s • deriv B s` loses one derivative on the open set `(0,∞)`
(`contDiffOn_succ_iff_deriv_of_isOpen`), so `(s∂_s)^k` maps `C^{k+m}` to `C^m`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Auxiliary: if `A` is `C^{k+m}` on `(0,∞)` then `(s∂_s)^k A` is `C^m` there. -/
theorem sDerivIter_contDiffOn_aux (A : ℝ → Mat3) :
    ∀ k m : ℕ, ContDiffOn ℝ ((k + m : ℕ) : WithTop ℕ∞) A (Ioi 0) →
      ContDiffOn ℝ (m : WithTop ℕ∞) (sDerivIter k A) (Ioi 0)
  | 0, m, h => by simpa [sDerivIter] using h
  | k + 1, m, h => by
    have e : k + 1 + m = k + (m + 1) := by omega
    have h' : ContDiffOn ℝ ((k + (m + 1) : ℕ) : WithTop ℕ∞) A (Ioi 0) := by
      rw [← e]; exact h
    have ih : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (sDerivIter k A) (Ioi 0) :=
      sDerivIter_contDiffOn_aux A k (m + 1) h'
    have ih' : ContDiffOn ℝ ((m : WithTop ℕ∞) + 1) (sDerivIter k A) (Ioi 0) := by
      rw [← Nat.cast_succ]; exact ih
    have hderiv : ContDiffOn ℝ (m : WithTop ℕ∞) (deriv (sDerivIter k A)) (Ioi 0) :=
      ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).1 ih').2.2
    have hfun : sDerivIter (k + 1) A = fun s => s • deriv (sDerivIter k A) s := rfl
    rw [hfun]
    exact contDiffOn_id.smul hderiv

/-- `C/env/1`: for `A` that is `C^6` on `(0,∞)`, `(s∂_s)^k A` is differentiable on `(0,∞)`
for every `k < 6`. -/
theorem sDerivIterDiffOn : SDerivIterDiffOn := by
  unfold SDerivIterDiffOn
  intro A hA k hk
  have h6 : ContDiffOn ℝ ((k + (6 - k) : ℕ) : WithTop ℕ∞) A (Ioi 0) := by
    have e : k + (6 - k) = 6 := by omega
    rw [e]
    exact_mod_cast hA
  have hC := sDerivIter_contDiffOn_aux A k (6 - k) h6
  exact hC.differentiableOn (by exact_mod_cast (show 6 - k ≠ 0 by omega))

end UnforcedLeray.Short.PartIIIb.Concrete
