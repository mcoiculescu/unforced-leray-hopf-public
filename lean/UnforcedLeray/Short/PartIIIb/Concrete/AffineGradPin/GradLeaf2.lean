import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.SDerivIterDiffOn
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.SDerivIterLeibniz

/-!
# `PartIII-b:C/grad/3/2`: conormal size of `(s∂_s)^j A^y`, `j ≤ 2` (source 4955-4962, 5063-5079)

The pointwise comparison `affSum 6 (A^y) s ≤ C_0 affSum 6 A s` on `0 < s ≤ 1.1/ν` is the one
used inside `affMEnvelope_of`, here stated on its own; the bound of the supremum `M(A)` needs
its boundedness on `(0, 1.1/ν]`, which comes from `IsAffElem.bdd`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem affSum_Ay_le_aux (χ : ℝ → ℝ) (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (ν : ℝ) (hν : 0 < ν) (as : ℝ) (A : ℝ → Mat3) (hA : IsAffElem as A) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν →
      affSum 6 (Ay ν χ A) s ≤ C0 * affSum 6 A s := by
  obtain ⟨K, hK0, hK⟩ := sDerivIterR_bound hχ
  have hfi : ∀ i, sDerivIterR i (fun t => χ (ν * t)) = fun s => sDerivIterR i χ (ν * s) :=
    sDerivIterR_comp_mul χ ν
  have hfd : ∀ i, Differentiable ℝ (sDerivIterR i (fun t => χ (ν * t))) := by
    intro i
    rw [hfi i]
    have hg : Differentiable ℝ (sDerivIterR i χ) :=
      (sDerivIterR_contDiff hχ i).differentiable (by simp)
    intro s
    exact (hg (ν * s)).comp s (differentiableAt_id.const_mul ν)
  have hAd : ∀ k : ℕ, k < 6 → DifferentiableOn ℝ (sDerivIter k A) (Ioi 0) :=
    sDerivIterDiffOn A hA.smooth
  refine ⟨(∑ j ∈ Finset.range (6 + 1), chooseSum j) * K,
    mul_nonneg (Finset.sum_nonneg fun j _ => chooseSum_nonneg j) hK0, ?_⟩
  intro s hs0 hsT
  have hνs : ν * s ∈ Icc (0 : ℝ) (11 / 10) := by
    refine ⟨by positivity, ?_⟩
    have := (le_div_iff₀ hν).1 hsT
    linarith
  have hterm : ∀ j ∈ Finset.range (6 + 1),
      frob (sDerivIter j (Ay ν χ A) s) ≤ chooseSum j * K * affSum 6 A s := by
    intro j hj
    have hj6 : j ≤ 6 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hL' := sDerivIterLeibniz (fun t => χ (ν * t)) A j hfd (fun k hk => hAd k (by omega)) hs0
    have hAy : Ay ν χ A = fun t => (fun t => χ (ν * t)) t • A t := rfl
    rw [hAy, hL']
    calc frob (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, j.choose ij.1 •
            (sDerivIterR ij.1 (fun t => χ (ν * t)) s • sDerivIter ij.2 A s))
        ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, frob (j.choose ij.1 •
            (sDerivIterR ij.1 (fun t => χ (ν * t)) s • sDerivIter ij.2 A s)) :=
          frob_sum_le _ _
      _ ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, (j.choose ij.1 : ℝ) * (K * affSum 6 A s) := by
          apply Finset.sum_le_sum
          intro ij hij
          have hij' := Finset.HasAntidiagonal.mem_antidiagonal.1 hij
          rw [← Nat.cast_smul_eq_nsmul ℝ, frob_smul, frob_smul,
            abs_of_nonneg (Nat.cast_nonneg _)]
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          have h1 : |sDerivIterR ij.1 (fun t => χ (ν * t)) s| ≤ K := by
            rw [hfi]
            exact hK ij.1 (by omega) _ hνs
          have h2 : frob (sDerivIter ij.2 A s) ≤ affSum 6 A s :=
            Finset.single_le_sum (f := fun k => frob (sDerivIter k A s))
              (fun k _ => frob_nonneg _) (Finset.mem_range.2 (by omega))
          exact mul_le_mul h1 h2 (frob_nonneg _) hK0
      _ = chooseSum j * K * affSum 6 A s := by
          rw [chooseSum, Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ => by ring
  show ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (Ay ν χ A) s) ≤
    ((∑ j ∈ Finset.range (6 + 1), chooseSum j) * K) * affSum 6 A s
  calc ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (Ay ν χ A) s)
      ≤ ∑ j ∈ Finset.range (6 + 1), chooseSum j * K * affSum 6 A s := Finset.sum_le_sum hterm
    _ = ((∑ j ∈ Finset.range (6 + 1), chooseSum j) * K) * affSum 6 A s := by
          rw [Finset.sum_mul, Finset.sum_mul]

/-- Conormal size (source 5063-5079): `|(s∂_s)^j A^y(s)| ≤ s^{5/2} M(A)` for `j ≤ 2`,
`0 < s ≤ 1.1/ν` (terms of the `sSup` defining `M(A)`). -/
theorem ayIterBound (as : ℝ) (χf : ℝ → ℝ) : AyIterBound as χf := by
  intro hχ ν hν A hA s hs hsT j hj
  obtain ⟨C0, hC0, hpt⟩ := affSum_Ay_le_aux χf hχ.smooth ν hν as A hA
  have hbdd : BddAbove ((fun s => s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) ''
      Ioc 0 ((11 / 10) / ν)) := by
    refine ⟨C0 * (Real.exp (|as| * ((11 / 10) / ν)) * affNorm as A), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have ht0 : 0 < t := ht.1
    have htT : t ≤ (11 / 10) / ν := ht.2
    have hterm_le : affTerm as 6 A t ≤ affNorm as A := le_csSup hA.bdd ⟨t, ht0, rfl⟩
    have hexp : Real.exp (as * t) ≤ Real.exp (|as| * ((11 / 10) / ν)) := by
      apply Real.exp_le_exp.2
      have h2 : as * t ≤ |as| * t := mul_le_mul_of_nonneg_right (le_abs_self as) ht0.le
      have h3 : |as| * t ≤ |as| * ((11 / 10) / ν) := mul_le_mul_of_nonneg_left htT (abs_nonneg _)
      linarith
    have hid : t ^ (-(5 / 2 : ℝ)) * affSum 6 A t = Real.exp (as * t) * affTerm as 6 A t := by
      unfold affTerm
      have h1 : Real.exp (as * t) * Real.exp (-as * t) = 1 := by
        rw [← Real.exp_add, show as * t + -as * t = 0 by ring, Real.exp_zero]
      calc t ^ (-(5 / 2 : ℝ)) * affSum 6 A t
          = (Real.exp (as * t) * Real.exp (-as * t)) * (t ^ (-(5 / 2 : ℝ)) * affSum 6 A t) := by
            rw [h1, one_mul]
        _ = _ := by ring
    have hrp : 0 ≤ t ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg ht0.le _
    show t ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) t ≤ _
    calc t ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) t
        ≤ t ^ (-(5 / 2 : ℝ)) * (C0 * affSum 6 A t) :=
          mul_le_mul_of_nonneg_left (hpt t ht0 htT) hrp
      _ = C0 * (Real.exp (as * t) * affTerm as 6 A t) := by rw [← hid]; ring
      _ ≤ C0 * (Real.exp (|as| * ((11 / 10) / ν)) * affNorm as A) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          exact mul_le_mul hexp hterm_le (affTerm_nonneg as 6 A t ht0) (Real.exp_pos _).le
  have hle : s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s ≤ affM ν χf A :=
    le_csSup hbdd ⟨s, ⟨hs, hsT⟩, rfl⟩
  have hfr : frob (sDerivIter j (Ay ν χf A) s) ≤ affSum 6 (Ay ν χf A) s := by
    unfold affSum
    exact Finset.single_le_sum (f := fun k => frob (sDerivIter k (Ay ν χf A) s))
      (fun k _ => frob_nonneg _) (Finset.mem_range.2 (by omega))
  have hp : s ^ (5 / 2 : ℝ) * s ^ (-(5 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hs]; norm_num
  calc frob (sDerivIter j (Ay ν χf A) s) ≤ affSum 6 (Ay ν χf A) s := hfr
    _ = s ^ (5 / 2 : ℝ) * (s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) := by
          rw [← mul_assoc, hp, one_mul]
    _ ≤ s ^ (5 / 2 : ℝ) * affM ν χf A := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hs.le _)

end UnforcedLeray.Short.PartIIIb.Concrete
