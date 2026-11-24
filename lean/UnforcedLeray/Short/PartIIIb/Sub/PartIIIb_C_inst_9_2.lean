import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9

/-!
# `PartIII-b:C/inst/9/2`: `AySumBdd` from the two conormal leaves

Source `the November 2 reference manuscript`
4955-4962, 5063-5079, 5089-5091.  With `SDerivIterDiffOn` and `SDerivIterLeibniz`
(tasks `PartIII-b:C/env/1`, `PartIII-b:C/env/2`, `Concrete/AffineEnvelope.lean`) the defining sum of
`M(A)` is bounded on `(0, 1.1/ν]` (this is `AySumBdd` of `FACoefBound/BmatBound.lean`, stated
here in unfolded form so that this file does not import it).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem aySumBdd_of (hD : SDerivIterDiffOn) (hL : SDerivIterLeibniz) (as : ℝ) (χf : ℝ → ℝ) :
    IsSourceCutoffC χf → ∀ ν : ℝ, 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
      BddAbove ((fun s => s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) '' Ioc 0 ((11 / 10) / ν)) := by
  intro hχ ν hν A hA
  obtain ⟨K, hK0, hK⟩ := sDerivIterR_bound hχ.smooth
  set C0 := (∑ j ∈ Finset.range (6 + 1), chooseSum j) * K with hC0
  have hC00 : 0 ≤ C0 :=
    mul_nonneg (Finset.sum_nonneg fun j _ => chooseSum_nonneg j) hK0
  have hfi : ∀ i, sDerivIterR i (fun t => χf (ν * t)) = fun s => sDerivIterR i χf (ν * s) :=
    sDerivIterR_comp_mul χf ν
  have hfd : ∀ i, Differentiable ℝ (sDerivIterR i (fun t => χf (ν * t))) := by
    intro i
    rw [hfi i]
    have hg : Differentiable ℝ (sDerivIterR i χf) :=
      (sDerivIterR_contDiff hχ.smooth i).differentiable (by simp)
    intro s
    exact (hg (ν * s)).comp s (differentiableAt_id.const_mul ν)
  have hAd : ∀ k : ℕ, k < 6 → DifferentiableOn ℝ (sDerivIter k A) (Ioi 0) := hD A hA.smooth
  have hpt : ∀ s ∈ Ioc (0 : ℝ) ((11 / 10) / ν), affSum 6 (Ay ν χf A) s ≤ C0 * affSum 6 A s := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hνs : ν * s ∈ Icc (0 : ℝ) (11 / 10) := by
      refine ⟨by positivity, ?_⟩
      have := (le_div_iff₀ hν).1 hs.2
      linarith
    have hterm : ∀ j ∈ Finset.range (6 + 1),
        frob (sDerivIter j (Ay ν χf A) s) ≤ chooseSum j * K * affSum 6 A s := by
      intro j hj
      have hj6 : j ≤ 6 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hL' := hL (fun t => χf (ν * t)) A j hfd (fun k hk => hAd k (by omega)) hs0
      have hAy : Ay ν χf A = fun t => (fun t => χf (ν * t)) t • A t := rfl
      rw [hAy, hL']
      calc frob (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, j.choose ij.1 •
              (sDerivIterR ij.1 (fun t => χf (ν * t)) s • sDerivIter ij.2 A s))
          ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, frob (j.choose ij.1 •
              (sDerivIterR ij.1 (fun t => χf (ν * t)) s • sDerivIter ij.2 A s)) :=
            frob_sum_le _ _
        _ ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, (j.choose ij.1 : ℝ) * (K * affSum 6 A s) := by
            apply Finset.sum_le_sum
            intro ij hij
            have hij' := Finset.HasAntidiagonal.mem_antidiagonal.1 hij
            rw [← Nat.cast_smul_eq_nsmul ℝ, frob_smul, frob_smul,
              abs_of_nonneg (Nat.cast_nonneg _)]
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            have h1 : |sDerivIterR ij.1 (fun t => χf (ν * t)) s| ≤ K := by
              rw [hfi]
              exact hK ij.1 (by omega) _ hνs
            have h2 : frob (sDerivIter ij.2 A s) ≤ affSum 6 A s :=
              Finset.single_le_sum (f := fun k => frob (sDerivIter k A s))
                (fun k _ => frob_nonneg _) (Finset.mem_range.2 (by omega))
            exact mul_le_mul h1 h2 (frob_nonneg _) hK0
        _ = chooseSum j * K * affSum 6 A s := by
            rw [chooseSum, Finset.sum_mul, Finset.sum_mul]
            exact Finset.sum_congr rfl fun _ _ => by ring
    show ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (Ay ν χf A) s) ≤ C0 * affSum 6 A s
    calc ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (Ay ν χf A) s)
        ≤ ∑ j ∈ Finset.range (6 + 1), chooseSum j * K * affSum 6 A s := Finset.sum_le_sum hterm
      _ = C0 * affSum 6 A s := by rw [hC0, ← Finset.sum_mul, ← Finset.sum_mul]
  obtain ⟨B, hB⟩ := hA.bdd
  refine ⟨C0 * Real.exp (|as| * ((11 / 10) / ν)) * B, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hs0 : 0 < s := hs.1
  have hterm_le : affTerm as 6 A s ≤ B := hB ⟨s, hs0, rfl⟩
  have hexp : Real.exp (as * s) ≤ Real.exp (|as| * ((11 / 10) / ν)) := by
    apply Real.exp_le_exp.2
    exact mul_le_mul (le_abs_self as) hs.2 hs0.le (abs_nonneg _)
  have hid : s ^ (-(5 / 2 : ℝ)) * affSum 6 A s = Real.exp (as * s) * affTerm as 6 A s := by
    unfold affTerm
    have h1 : Real.exp (as * s) * Real.exp (-as * s) = 1 := by
      rw [← Real.exp_add, show as * s + -as * s = 0 by ring, Real.exp_zero]
    calc s ^ (-(5 / 2 : ℝ)) * affSum 6 A s
        = (Real.exp (as * s) * Real.exp (-as * s)) * (s ^ (-(5 / 2 : ℝ)) * affSum 6 A s) := by
          rw [h1, one_mul]
      _ = _ := by ring
  have hrp : 0 ≤ s ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hs0.le _
  calc s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s
      ≤ s ^ (-(5 / 2 : ℝ)) * (C0 * affSum 6 A s) := mul_le_mul_of_nonneg_left (hpt s hs) hrp
    _ = C0 * (Real.exp (as * s) * affTerm as 6 A s) := by rw [← hid]; ring
    _ ≤ C0 * (Real.exp (|as| * ((11 / 10) / ν)) * B) := by
        apply mul_le_mul_of_nonneg_left _ hC00
        exact mul_le_mul hexp hterm_le (affTerm_nonneg as 6 A s hs0) (Real.exp_pos _).le
    _ = C0 * Real.exp (|as| * ((11 / 10) / ν)) * B := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
