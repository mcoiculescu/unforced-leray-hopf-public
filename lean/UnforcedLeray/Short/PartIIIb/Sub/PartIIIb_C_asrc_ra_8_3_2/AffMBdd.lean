import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_2
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.SDerivIterDiffOn
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.SDerivIterLeibniz

/-!
# `PartIII-b:C/asrc/ra/8/3/2/3` : `M(A)` is a finite supremum (`AffMBdd`)

Source: `the November 2 reference manuscript` 4955-4962 (`M(A)`, `A^y = χ_f A`),
4750-4760.

Proof.  For `0 < s ≤ 1.1/ν`, the Leibniz rule for `s∂_s` together with the dilation bound on
`(t∂_t)^i χ` (`sDerivIterR_bound`) gives `affSum 6 (A^y) s ≤ C₀ affSum 6 A s`, the same comparison
as in `affMEnvelope_of`.  Since `s^{-5/2} affSum 6 A s = e^{as s} affTerm as 6 A s` and
`affTerm as 6 A s ≤ affNorm as A` (from `IsAffElem.bdd`), every element of the image is bounded
by `C₀ e^{|as| 1.1/ν} affNorm as A`.
-/

set_option autoImplicit false

noncomputable section

open Set Real
open scoped BigOperators

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Pointwise comparison `affSum 6 (A^y) s ≤ C₀ affSum 6 A s` on `(0, 1.1/ν]` (the first half of
`affMEnvelope_of`, with the constant `C₀ = (Σ_j chooseSum j) K`). -/
theorem affSum_Ay_le_of_cutoff (as : ℝ) {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) {ν : ℝ} (hν : 0 < ν)
    (A : ℝ → Mat3) (hA : IsAffElem as A) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ s ∈ Ioc (0 : ℝ) ((11 / 10) / ν),
      affSum 6 (Ay ν χf A) s ≤ C0 * affSum 6 A s := by
  obtain ⟨K, hK0, hK⟩ := sDerivIterR_bound hχ.smooth
  have hC00 : 0 ≤ (∑ j ∈ Finset.range (6 + 1), chooseSum j) * K :=
    mul_nonneg (Finset.sum_nonneg fun j _ => chooseSum_nonneg j) hK0
  refine ⟨(∑ j ∈ Finset.range (6 + 1), chooseSum j) * K, hC00, ?_⟩
  set C0 := (∑ j ∈ Finset.range (6 + 1), chooseSum j) * K with hC0
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
    sDerivIterDiffOn A hA.smooth
  intro s hs
  have hs0 : 0 < s := hs.1
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
            refine hK ij.1 (by omega) _ ⟨by positivity, ?_⟩
            have := (le_div_iff₀ hν).1 hs.2
            linarith
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

/-- **Leaf (ii): `M(A)` is a finite supremum** (source 4955-4962). -/
theorem affMBdd (as : ℝ) (χf : ℝ → ℝ) : AffMBdd as χf := by
  intro hχ ν hν A hA
  obtain ⟨C0, hC0, hpt⟩ := affSum_Ay_le_of_cutoff as hχ hν A hA
  set B : ℝ := |as| * ((11 / 10) / ν) with hB
  refine ⟨C0 * (Real.exp B * affNorm as A), ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hs0 : 0 < s := hs.1
  have hterm_le : affTerm as 6 A s ≤ affNorm as A := le_csSup hA.bdd ⟨s, hs0, rfl⟩
  have hterm_nn : 0 ≤ affTerm as 6 A s := affTerm_nonneg as 6 A s hs0
  have hexp : Real.exp (as * s) ≤ Real.exp B := by
    apply Real.exp_le_exp.2
    have h1 : s ≤ (11 / 10) / ν := hs.2
    have h2 : as * s ≤ |as| * s := by
      have := le_abs_self as
      nlinarith [abs_nonneg as, hs0]
    have h3 : |as| * s ≤ |as| * ((11 / 10) / ν) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg as)
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
  have hmid : Real.exp (as * s) * affTerm as 6 A s ≤ Real.exp B * affNorm as A :=
    mul_le_mul hexp hterm_le hterm_nn (Real.exp_pos _).le
  calc s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s
      ≤ s ^ (-(5 / 2 : ℝ)) * (C0 * affSum 6 A s) := mul_le_mul_of_nonneg_left (hpt s hs) hrp
    _ = C0 * (Real.exp (as * s) * affTerm as 6 A s) := by rw [← hid]; ring
    _ ≤ C0 * (Real.exp B * affNorm as A) := mul_le_mul_of_nonneg_left hmid hC0

end UnforcedLeray.Short.PartIIIb.Concrete
