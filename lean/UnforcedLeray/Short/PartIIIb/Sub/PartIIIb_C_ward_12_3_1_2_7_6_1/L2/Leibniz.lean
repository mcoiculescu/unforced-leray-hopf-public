import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Leibniz bounds of order `0, 1, 2` on an open set

Source `the November 2 reference manuscript`
lines 2360-2366 (product rule for the ring lift `√s • frame (b ∘ chart)`).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem clm_apply_le {U : Set E} (hU : IsOpen U) {y : E} (hy : y ∈ U) {P : E → F →L[ℝ] G}
    {B : E → F} (hP : ContDiffOn ℝ ∞ P U) (hB : ContDiffOn ℝ ∞ B U) :
    ‖iteratedFDeriv ℝ 0 (fun z => P z (B z)) y‖ ≤
        ‖iteratedFDeriv ℝ 0 P y‖ * ‖iteratedFDeriv ℝ 0 B y‖ ∧
    ‖iteratedFDeriv ℝ 1 (fun z => P z (B z)) y‖ ≤
        ‖iteratedFDeriv ℝ 0 P y‖ * ‖iteratedFDeriv ℝ 1 B y‖ +
          ‖iteratedFDeriv ℝ 1 P y‖ * ‖iteratedFDeriv ℝ 0 B y‖ ∧
    ‖iteratedFDeriv ℝ 2 (fun z => P z (B z)) y‖ ≤
        ‖iteratedFDeriv ℝ 0 P y‖ * ‖iteratedFDeriv ℝ 2 B y‖ +
          2 * (‖iteratedFDeriv ℝ 1 P y‖ * ‖iteratedFDeriv ℝ 1 B y‖) +
          ‖iteratedFDeriv ℝ 2 P y‖ * ‖iteratedFDeriv ℝ 0 B y‖ := by
  have key : ∀ n : ℕ, ‖iteratedFDeriv ℝ n (fun z => P z (B z)) y‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i P y‖ *
        ‖iteratedFDeriv ℝ (n - i) B y‖ := by
    intro n
    have h := norm_iteratedFDerivWithin_clm_apply hP hB hU.uniqueDiffOn hy (n := n)
      (by exact_mod_cast le_top)
    simp only [iteratedFDerivWithin_of_isOpen _ hU hy] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · have := key 0
    simpa using this
  · have := key 1
    simp [Finset.sum_range_succ] at this ⊢
    linarith
  · have := key 2
    simp [Finset.sum_range_succ, Nat.choose] at this ⊢
    linarith

theorem smul_le {U : Set E} (hU : IsOpen U) {y : E} (hy : y ∈ U) {f : E → ℝ} {g : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    ‖iteratedFDeriv ℝ 1 (fun z => f z • g z) y‖ ≤
        ‖iteratedFDeriv ℝ 0 f y‖ * ‖iteratedFDeriv ℝ 1 g y‖ +
          ‖iteratedFDeriv ℝ 1 f y‖ * ‖iteratedFDeriv ℝ 0 g y‖ ∧
    ‖iteratedFDeriv ℝ 2 (fun z => f z • g z) y‖ ≤
        ‖iteratedFDeriv ℝ 0 f y‖ * ‖iteratedFDeriv ℝ 2 g y‖ +
          2 * (‖iteratedFDeriv ℝ 1 f y‖ * ‖iteratedFDeriv ℝ 1 g y‖) +
          ‖iteratedFDeriv ℝ 2 f y‖ * ‖iteratedFDeriv ℝ 0 g y‖ := by
  have key : ∀ n : ℕ, ‖iteratedFDeriv ℝ n (fun z => f z • g z) y‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (n - i) g y‖ := by
    intro n
    have h := norm_iteratedFDerivWithin_smul_le hf hg hU.uniqueDiffOn hy (n := n)
      (by exact_mod_cast le_top)
    simp only [iteratedFDerivWithin_of_isOpen _ hU hy] at h
    exact h
  refine ⟨?_, ?_⟩
  · have := key 1
    simp [Finset.sum_range_succ] at this ⊢
    linarith
  · have := key 2
    simp [Finset.sum_range_succ, Nat.choose] at this ⊢
    linarith

end

end UnforcedLeray.Short.PartIIIb.Concrete
