import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.Envelope
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.BmatBound

/-!
# Pointwise conormal bound of `B = Bmat ν μ χ A` with the exponential weight (source 4863-4864)

For `A ∈ 𝒜` and `0 < s ≤ 1.1/ν`: `|B(s)| ≤ (1+μ) C₀ s^{3/2} e^{a_s s} ‖A‖_𝒜`, `C₀` depending only on
the cutoff profile (the pointwise form of the envelope `affMEnvelope`, source 5089-5091).
-/

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The pointwise Leibniz comparison `Σ_j |(s∂)^j(χ A)| ≤ C₀ Σ_k |(s∂)^k A|` for `νs ≤ 1.1`. -/
theorem affSum_Ay_le {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (ν : ℝ) (A : ℝ → Mat3), 0 < ν → ContDiffOn ℝ 6 A (Ioi 0) →
      ∀ s ∈ Ioc (0 : ℝ) ((11 / 10) / ν), affSum 6 (Ay ν χ A) s ≤ C0 * affSum 6 A s := by
  obtain ⟨K, hK0, hK⟩ := sDerivIterR_bound hχ.smooth
  have hC00 : 0 ≤ (∑ j ∈ Finset.range (6 + 1), chooseSum j) * K :=
    mul_nonneg (Finset.sum_nonneg fun j _ => chooseSum_nonneg j) hK0
  refine ⟨(∑ j ∈ Finset.range (6 + 1), chooseSum j) * K, hC00, ?_⟩
  intro ν A hν hAs s hs
  set C0 := (∑ j ∈ Finset.range (6 + 1), chooseSum j) * K with hC0
  have hfi : ∀ i, sDerivIterR i (fun t => χ (ν * t)) = fun s => sDerivIterR i χ (ν * s) :=
    sDerivIterR_comp_mul χ ν
  have hfd : ∀ i, Differentiable ℝ (sDerivIterR i (fun t => χ (ν * t))) := by
    intro i
    rw [hfi i]
    have hg : Differentiable ℝ (sDerivIterR i χ) :=
      (sDerivIterR_contDiff hχ.smooth i).differentiable (by simp)
    intro s
    exact (hg (ν * s)).comp s (differentiableAt_id.const_mul ν)
  have hAd : ∀ k : ℕ, k < 6 → DifferentiableOn ℝ (sDerivIter k A) (Ioi 0) :=
    sDerivIterDiffOn A hAs
  have hs0 : 0 < s := hs.1
  have hνs : ν * s ∈ Icc (0 : ℝ) (11 / 10) := by
    refine ⟨by positivity, ?_⟩
    have := (le_div_iff₀ hν).1 hs.2
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
  show ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (Ay ν χ A) s) ≤ C0 * affSum 6 A s
  calc ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (Ay ν χ A) s)
      ≤ ∑ j ∈ Finset.range (6 + 1), chooseSum j * K * affSum 6 A s := Finset.sum_le_sum hterm
    _ = C0 * affSum 6 A s := by rw [hC0, ← Finset.sum_mul, ← Finset.sum_mul]

/-- `Σ_k |(s∂)^k A(s)| ≤ s^{5/2} e^{a s} ‖A‖_𝒜`. -/
theorem affSum_le_affNorm {as : ℝ} {A : ℝ → Mat3} (hA : IsAffElem as A) {s : ℝ} (hs : 0 < s) :
    affSum 6 A s ≤ s ^ (5 / 2 : ℝ) * Real.exp (as * s) * affNorm as A := by
  have hterm_le : affTerm as 6 A s ≤ affNorm as A := le_csSup hA.bdd ⟨s, hs, rfl⟩
  have hpos : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hid : affSum 6 A s = s ^ (5 / 2 : ℝ) * Real.exp (as * s) * affTerm as 6 A s := by
    unfold affTerm
    have h1 : Real.exp (as * s) * Real.exp (-as * s) = 1 := by
      rw [← Real.exp_add, show as * s + -as * s = 0 by ring, Real.exp_zero]
    have h2 : s ^ (5 / 2 : ℝ) * s ^ (-(5 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hs]; simp
    calc affSum 6 A s = (Real.exp (as * s) * Real.exp (-as * s)) *
          (s ^ (5 / 2 : ℝ) * s ^ (-(5 / 2 : ℝ))) * affSum 6 A s := by rw [h1, h2]; ring
      _ = _ := by ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left hterm_le (mul_nonneg hpos.le (Real.exp_pos _).le)

/-- The pointwise exponentially weighted bound of `B`. -/
theorem bmat_pointwise {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (as ν μ : ℝ) (A : ℝ → Mat3), 0 < ν → 0 ≤ μ → IsAffElem as A →
      ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν →
        frob (Bmat ν μ χ A s) ≤ (1 + μ) * C0 * (s ^ (3 / 2 : ℝ) * Real.exp (as * s)) *
          affNorm as A := by
  obtain ⟨C0, hC0, hpt⟩ := affSum_Ay_le hχ
  refine ⟨C0, hC0, ?_⟩
  intro as ν μ A hν hμ hA s hs hsT
  have hge := fac_affSum_ge (Ay ν χ A) s
  have e0 : sDerivIter 0 (Ay ν χ A) s = Ay ν χ A s := rfl
  have e1 : sDerivIter 1 (Ay ν χ A) s = s • deriv (Ay ν χ A) s := rfl
  rw [e0, e1] at hge
  have hS1 := hpt ν A hν hA.smooth s ⟨hs, hsT⟩
  have hS2 := affSum_le_affNorm hA hs
  have hn := affNorm_nonneg as A hA
  have hμ1 : 0 ≤ 1 + μ := by linarith
  have h1 := fac_frob_add_le (s • deriv (Ay ν χ A) s) (μ • Ay ν χ A s)
  rw [fac_frob_smul μ (Ay ν χ A s), abs_of_nonneg hμ] at h1
  have hnn1 : 0 ≤ μ * frob (Ay ν χ A s) := mul_nonneg hμ (fac_frob_nonneg _)
  have hnn2 : 0 ≤ frob (s • deriv (Ay ν χ A) s) := fac_frob_nonneg _
  have hnn3 : 0 ≤ frob (Ay ν χ A s) := fac_frob_nonneg _
  have hk2 : (1 + μ) * (frob (Ay ν χ A s) + frob (s • deriv (Ay ν χ A) s)) ≤
      (1 + μ) * affSum 6 (Ay ν χ A) s := mul_le_mul_of_nonneg_left hge hμ1
  have hB1 : frob (s • deriv (Ay ν χ A) s + μ • Ay ν χ A s) ≤
      (1 + μ) * affSum 6 (Ay ν χ A) s := by nlinarith [h1, hk2, hnn1, hnn2, hnn3]
  have hchain : affSum 6 (Ay ν χ A) s ≤ C0 * (s ^ (5 / 2 : ℝ) * Real.exp (as * s) * affNorm as A) :=
    hS1.trans (mul_le_mul_of_nonneg_left hS2 hC0)
  rw [fac_Bmat_eq ν μ χ A s hs, fac_frob_smul, abs_of_pos (inv_pos.2 hs)]
  have hs52 : s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) * s := fac_s52 s hs
  calc s⁻¹ * frob (s • deriv (Ay ν χ A) s + μ • Ay ν χ A s)
      ≤ s⁻¹ * ((1 + μ) * (C0 * (s ^ (5 / 2 : ℝ) * Real.exp (as * s) * affNorm as A))) :=
        mul_le_mul_of_nonneg_left (hB1.trans (mul_le_mul_of_nonneg_left hchain hμ1))
          (inv_nonneg.2 hs.le)
    _ = (1 + μ) * C0 * (s ^ (3 / 2 : ℝ) * Real.exp (as * s)) * affNorm as A := by
        rw [hs52]
        field_simp

end UnforcedLeray.Short.PartIIIb.Concrete
