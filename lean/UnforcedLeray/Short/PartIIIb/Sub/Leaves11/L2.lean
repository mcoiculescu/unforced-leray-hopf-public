import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.BmatBound

/-!
# `PartIII-b:C/inst/11/2`: `AyDerivBound` (the `j = 1` term of `M(A)`)

Source `the November 2 reference manuscript` 4953-4963, 5063-5079.

`fac_frob_Ay_le` (`FACoefBound/BmatBound.lean`) already gives
`|A^y(s)| + |s∂_sA^y(s)| ≤ s^{5/2} M(A)` from `BddAbove` of the defining supremum (`AySumBdd`).
Here `AySumBdd` is proved, by the same Leibniz/dilation argument as `affMEnvelope_of`
(`Concrete/AffineEnvelope.lean`), with the constant `|as|` in place of `1.1 a_s/ν`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem aySumBdd_inst11 (as : ℝ) (χf : ℝ → ℝ) : AySumBdd as χf := by
  intro hχ ν hν A hA
  obtain ⟨K, hK0, hK⟩ := sDerivIterR_bound hχ.smooth
  set C0 : ℝ := (∑ j ∈ Finset.range (6 + 1), chooseSum j) * K with hC0
  have hC00 : 0 ≤ C0 := mul_nonneg (Finset.sum_nonneg fun j _ => chooseSum_nonneg j) hK0
  have hfi : ∀ i, sDerivIterR i (fun t => χf (ν * t)) = fun s => sDerivIterR i χf (ν * s) :=
    sDerivIterR_comp_mul χf ν
  have hfd : ∀ i, Differentiable ℝ (sDerivIterR i (fun t => χf (ν * t))) := by
    intro i
    rw [hfi i]
    have hg : Differentiable ℝ (sDerivIterR i χf) :=
      (sDerivIterR_contDiff hχ.smooth i).differentiable (by simp)
    intro s
    exact (hg (ν * s)).comp s (differentiableAt_id.const_mul ν)
  have hAd : ∀ k : ℕ, k < 6 → DifferentiableOn ℝ (sDerivIter k A) (Ioi 0) :=
    fun k hk => sDerivIterDiffOn A hA.smooth k hk
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
      have hL' := sDerivIterLeibniz (fun t => χf (ν * t)) A j hfd
        (fun k hk => hAd k (by omega)) hs0
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
  have hbdd : BddAbove ((fun s => s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) ''
      Ioc 0 ((11 / 10) / ν)) := by
    refine ⟨C0 * (Real.exp (|as| * ((11 / 10) / ν)) * affNorm as A), ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hs0 : 0 < s := hs.1
    have hsT : s ≤ (11 / 10) / ν := hs.2
    have hterm_le : affTerm as 6 A s ≤ affNorm as A := le_csSup hA.bdd ⟨s, hs0, rfl⟩
    have hexp : Real.exp (as * s) ≤ Real.exp (|as| * ((11 / 10) / ν)) := by
      apply Real.exp_le_exp.2
      have h1 : as * s ≤ |as| * s := mul_le_mul_of_nonneg_right (le_abs_self as) hs0.le
      have h2 : |as| * s ≤ |as| * ((11 / 10) / ν) := mul_le_mul_of_nonneg_left hsT (abs_nonneg as)
      linarith
    have hid : s ^ (-(5 / 2 : ℝ)) * affSum 6 A s = Real.exp (as * s) * affTerm as 6 A s := by
      unfold affTerm
      have h1 : Real.exp (as * s) * Real.exp (-as * s) = 1 := by
        rw [← Real.exp_add, show as * s + -as * s = 0 by ring, Real.exp_zero]
      calc s ^ (-(5 / 2 : ℝ)) * affSum 6 A s
          = (Real.exp (as * s) * Real.exp (-as * s)) * (s ^ (-(5 / 2 : ℝ)) * affSum 6 A s) := by
            rw [h1, one_mul]
        _ = _ := by ring
    have hrp : 0 ≤ s ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hs0.le _
    have hnn : 0 ≤ affTerm as 6 A s := affTerm_nonneg as 6 A s hs0
    calc s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s
        ≤ s ^ (-(5 / 2 : ℝ)) * (C0 * affSum 6 A s) := mul_le_mul_of_nonneg_left (hpt s hs) hrp
      _ = C0 * (Real.exp (as * s) * affTerm as 6 A s) := by rw [← hid]; ring
      _ ≤ C0 * (Real.exp (|as| * ((11 / 10) / ν)) * affNorm as A) := by
          apply mul_le_mul_of_nonneg_left _ hC00
          exact mul_le_mul hexp hterm_le hnn (Real.exp_pos _).le
  exact hbdd

theorem ayDerivBound (as : ℝ) (χf : ℝ → ℝ) : AyDerivBound as χf := by
  unfold AyDerivBound
  intro hχ ν hν A hA s hs hsT
  have hk := fac_frob_Ay_le ν χf A (aySumBdd_inst11 as χf hχ ν hν A hA) s hs hsT
  show frob (s • deriv (Ay ν χf A) s) ≤ s ^ (5 / 2 : ℝ) * affM ν χf A
  linarith [fac_frob_nonneg (Ay ν χf A s)]

end UnforcedLeray.Short.PartIIIb.Concrete
