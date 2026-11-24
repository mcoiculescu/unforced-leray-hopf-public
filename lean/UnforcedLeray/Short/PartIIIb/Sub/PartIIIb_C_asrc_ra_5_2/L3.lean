import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_2.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_2.L2
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# `PartIII-b:C/asrc/ra/5/2/3` : the bound `GaussQBound` for `q = |x|² (κ a)⁻¹`

Source 4963-4968.  Leibniz rule on the open slab `{p | 0 < p.1}` for the product of
`sq2 p.2` (L1) and `(κ a(p.1))⁻¹` (L2).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set

theorem gaussQBound_proof (κ ν s0 s1 : ℝ) : GaussQBound κ ν s0 s1 := by
  intro hκ hν hs0 hs01 j
  choose C1 hC1n hC1 using gauss_sq2_iterated_bound
  have hage := fun k : ℕ => gauss_age_iterated_bound κ ν s0 s1 hκ hν hs0 hs01 k
  choose C2 hC2n hC2 using hage
  have hUo : IsOpen (((Prod.fst : ℝ × (ℝ × ℝ) → ℝ) ⁻¹' Ioi (0 : ℝ))) := isOpen_Ioi.preimage continuous_fst
  have hUD : UniqueDiffOn ℝ (((Prod.fst : ℝ × (ℝ × ℝ) → ℝ) ⁻¹' Ioi (0 : ℝ))) := hUo.uniqueDiffOn
  have hf : ContDiff ℝ (j : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => sq2 p.2) := by
    unfold sq2
    fun_prop
  have hc : ContDiff ℝ (j : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => κ * ageA ν p.1) := by
    unfold ageA
    fun_prop
  have hg : ContDiffOn ℝ (j : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => (κ * ageA ν p.1)⁻¹)
      (((Prod.fst : ℝ × (ℝ × ℝ) → ℝ) ⁻¹' Ioi (0 : ℝ))) := by
    refine hc.contDiffOn.inv ?_
    intro p hp
    have hp' : (0 : ℝ) < p.1 := hp
    have : 0 < ageA ν p.1 := by
      unfold ageA
      nlinarith [mul_pos hν hp']
    exact (mul_pos hκ this).ne'
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * C1 i * C2 (j - i), ?_, ?_⟩
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC1n i)) (hC2n _)
  intro s hs x
  have hsp : (s, x) ∈ ((Prod.fst : ℝ × (ℝ × ℝ) → ℝ) ⁻¹' Ioi (0 : ℝ)) := by
    show (0 : ℝ) < s
    exact lt_of_lt_of_le hs0 hs.1
  show ‖iteratedFDeriv ℝ j (fun p : ℝ × (ℝ × ℝ) => sq2 p.2 * (κ * ageA ν p.1)⁻¹) (s, x)‖ ≤ _
  rw [← iteratedFDerivWithin_of_isOpen j hUo hsp]
  refine le_trans (norm_iteratedFDerivWithin_mul_le hf.contDiffOn hg hUD hsp le_rfl) ?_
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (fun p : ℝ × (ℝ × ℝ) => sq2 p.2)
          (((Prod.fst : ℝ × (ℝ × ℝ) → ℝ) ⁻¹' Ioi (0 : ℝ))) (s, x)‖ *
        ‖iteratedFDerivWithin ℝ (j - i) (fun p : ℝ × (ℝ × ℝ) => (κ * ageA ν p.1)⁻¹)
          (((Prod.fst : ℝ × (ℝ × ℝ) → ℝ) ⁻¹' Ioi (0 : ℝ))) (s, x)‖ ≤
      (j.choose i : ℝ) * (C1 i * (1 + sq2 x)) * C2 (j - i) := by
    intro i _
    rw [iteratedFDerivWithin_of_isOpen i hUo hsp, iteratedFDerivWithin_of_isOpen (j - i) hUo hsp]
    have hc : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
    have h1 := hC1 i (s, x)
    have h2 := hC2 (j - i) s hs x
    have h3 : (0 : ℝ) ≤ C1 i * (1 + sq2 x) := mul_nonneg (hC1n i) (by unfold sq2; positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (norm_nonneg _)
      (mul_nonneg hc h3)
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
