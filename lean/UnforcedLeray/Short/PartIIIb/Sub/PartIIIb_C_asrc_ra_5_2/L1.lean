import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# `PartIII-b:C/asrc/ra/5/2/1` : polynomial bound for `sq2 p.2`

Source 4963-4968.  The function `p ↦ sq2 p.2 = p.2.1 ^ 2 + p.2.2 ^ 2` is a sum of two squares of
continuous linear functionals on `ℝ × (ℝ × ℝ)`.  Every iterated derivative of order at least
three vanishes, and the orders `0, 1, 2` are bounded by `2 (1 + L p ^ 2)` per square.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set

/-- The first coordinate of the meridional part, `p ↦ p.2.1`. -/
def auxL1 : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The second coordinate of the meridional part, `p ↦ p.2.2`. -/
def auxL2 : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

theorem auxL1_apply (p : ℝ × (ℝ × ℝ)) : auxL1 p = p.2.1 := rfl

theorem auxL2_apply (p : ℝ × (ℝ × ℝ)) : auxL2 p = p.2.2 := rfl

theorem auxL1_norm_le : ‖auxL1‖ ≤ 1 := by
  calc ‖auxL1‖ ≤ ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ * ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 := mul_le_one₀ (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ) (norm_nonneg _)
        (ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ))

theorem auxL2_norm_le : ‖auxL2‖ ≤ 1 := by
  calc ‖auxL2‖ ≤ ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ * ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 := mul_le_one₀ (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ) (norm_nonneg _)
        (ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ))

/-- Derivatives of order at least two of a continuous linear functional vanish. -/
theorem aux_clm_iter_ge_two {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : G →L[ℝ] ℝ) (n : ℕ) (x : G) :
    ‖iteratedFDeriv ℝ (n + 1 + 1) L x‖ = 0 := by
  have h : ‖iteratedFDeriv ℝ (n + 1) (fderiv ℝ L) x‖ = ‖iteratedFDeriv ℝ (n + 1 + 1) L x‖ :=
    norm_iteratedFDeriv_fderiv
  have hf : fderiv ℝ L = fun _ => L := funext fun y => L.fderiv
  have h0 : iteratedFDeriv ℝ (n + 1) (fun _ : G => L) = 0 :=
    iteratedFDeriv_const_of_ne (by omega) L
  rw [hf, h0, Pi.zero_apply, norm_zero] at h
  exact h.symm

/-- The square of a continuous linear functional: its iterated derivatives are bounded by
`2 (1 + L p ^ 2)`. -/
theorem aux_sq_iter_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : G →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (n : ℕ) (x : G) :
    ‖iteratedFDeriv ℝ n (fun y => L y * L y) x‖ ≤ 2 * (1 + (L x) ^ 2) := by
  have hmul : ‖iteratedFDeriv ℝ n (fun y => L y * L y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i L x‖ *
        ‖iteratedFDeriv ℝ (n - i) L x‖ :=
    norm_iteratedFDeriv_mul_le (N := ((n : ℕ) : WithTop ℕ∞)) L.contDiff L.contDiff x le_rfl
  have hD1 : ‖iteratedFDeriv ℝ 1 L x‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_one, L.fderiv]
    exact hL
  have hsq : |L x| * |L x| = (L x) ^ 2 := by rw [abs_mul_abs_self]; ring
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | rfl | h3
  · rw [norm_iteratedFDeriv_zero, norm_mul, Real.norm_eq_abs, hsq]
    nlinarith [sq_nonneg (L x)]
  · have e1 : (1 - 0 : ℕ) = 1 := rfl
    have e2 : (1 - 1 : ℕ) = 0 := rfl
    have c0 : Nat.choose 1 0 = 1 := rfl
    have c1 : Nat.choose 1 1 = 1 := rfl
    rw [Finset.sum_range_succ, Finset.sum_range_one, e1, e2, norm_iteratedFDeriv_zero, c0,
      c1] at hmul
    simp only [Nat.cast_one, one_mul, Real.norm_eq_abs] at hmul
    have hL0 : 0 ≤ ‖iteratedFDeriv ℝ 1 L x‖ := norm_nonneg _
    nlinarith [sq_nonneg (|L x| - 1), sq_abs (L x), abs_nonneg (L x),
      mul_nonneg (abs_nonneg (L x)) (sub_nonneg.2 hD1)]
  · have h2 : ‖iteratedFDeriv ℝ 2 L x‖ = 0 := aux_clm_iter_ge_two L 0 x
    norm_num [Finset.sum_range_succ, norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.choose,
      h2] at hmul
    have hL0 : 0 ≤ ‖iteratedFDeriv ℝ 1 L x‖ := norm_nonneg _
    nlinarith [sq_nonneg (L x), sq_nonneg (|L x| - 1), sq_abs (L x), abs_nonneg (L x),
      mul_nonneg hL0 (sub_nonneg.2 hD1)]
  · have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i L x‖ *
        ‖iteratedFDeriv ℝ (n - i) L x‖ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      rcases (show i ≤ 1 ∨ 2 ≤ i by omega) with hi1 | hi2
      · obtain ⟨m, hm⟩ : ∃ m, n - i = m + 1 + 1 := ⟨n - i - 2, by omega⟩
        rw [hm, aux_clm_iter_ge_two L m x]
        simp
      · obtain ⟨m, hm⟩ : ∃ m, i = m + 1 + 1 := ⟨i - 2, by omega⟩
        rw [hm, aux_clm_iter_ge_two L m x]
        simp
    rw [hsum] at hmul
    nlinarith [sq_nonneg (L x)]

/-- `sq2 p.2` as a sum of two squares. -/
theorem auxSq2_eq (p : ℝ × (ℝ × ℝ)) : sq2 p.2 = auxL1 p * auxL1 p + auxL2 p * auxL2 p := by
  rw [auxL1_apply, auxL2_apply, sq2]
  ring

theorem gauss_sq2_iterated_bound : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × (ℝ × ℝ), ‖iteratedFDeriv ℝ j (fun p : ℝ × (ℝ × ℝ) => sq2 p.2) p‖ ≤ C * (1 + sq2 p.2) := by
  intro j
  refine ⟨4, by norm_num, fun p => ?_⟩
  have hfun : (fun p : ℝ × (ℝ × ℝ) => sq2 p.2) =
      (fun q : ℝ × (ℝ × ℝ) => auxL1 q * auxL1 q) + (fun q : ℝ × (ℝ × ℝ) => auxL2 q * auxL2 q) := by
    funext q
    simp only [Pi.add_apply]
    exact auxSq2_eq q
  have hA : ContDiff ℝ j (fun q : ℝ × (ℝ × ℝ) => auxL1 q * auxL1 q) :=
    auxL1.contDiff.mul auxL1.contDiff
  have hB : ContDiff ℝ j (fun q : ℝ × (ℝ × ℝ) => auxL2 q * auxL2 q) :=
    auxL2.contDiff.mul auxL2.contDiff
  rw [hfun, iteratedFDeriv_add_apply (hA.contDiffAt) (hB.contDiffAt)]
  have h1 := aux_sq_iter_bound auxL1 auxL1_norm_le j p
  have h2 := aux_sq_iter_bound auxL2 auxL2_norm_le j p
  have hsum := norm_add_le (iteratedFDeriv ℝ j (fun q : ℝ × (ℝ × ℝ) => auxL1 q * auxL1 q) p)
    (iteratedFDeriv ℝ j (fun q : ℝ × (ℝ × ℝ) => auxL2 q * auxL2 q) p)
  rw [auxL1_apply] at h1
  rw [auxL2_apply] at h2
  have hs : sq2 p.2 = p.2.1 ^ 2 + p.2.2 ^ 2 := rfl
  rw [hs]
  nlinarith [sq_nonneg p.2.1, sq_nonneg p.2.2]

end UnforcedLeray.Short.PartIIIb.Concrete
