import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9_2
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.SDerivIterDiffOn
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.SDerivIterLeibniz

/-!
# `PartIII-b:C/inst/9/2`: conormal size of `B = s⁻¹((s∂_s)A^y + μA^y)`

Source `the November 2 reference manuscript` 5009-5016, 5063-5079, 4953-4963.

Proved here (no sorry):

* frobenius algebra: `frob_smul`, triangle inequality `fac_frob_add_le`;
* `fac_affSum_ge` : the `j = 0, 1` terms of `affSum 6` are below `affSum 6`;
* `fac_frob_Ay_le` : given boundedness of the defining sup of `affM` (see `AySumBdd`),
  `|A^y(s)| + |s ∂_s A^y(s)| ≤ s^{5/2} M(A)` on `0 < s ≤ 1.1/ν`;
* `fac_Bmat_eq` : `B(s) = s⁻¹ • ((s•∂_s)A^y + μ A^y)`;
* `bmatBound_of_aySumBdd` : `BmatBound` from `AySumBdd`.

Missing leaf (reported, not proved here): `AySumBdd`, the boundedness of
`s ↦ s^{-5/2} Σ_{j≤6} |(s∂_s)^j (χ_f A)(s)|` on `(0, 1.1/ν]`, which needs the Leibniz rule for
`s∂_s` on `χ_f(s) A(s)` together with boundedness of `(s∂_s)^i χ_f(νs)` on `(0,1.1/ν]`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Named leaf: the defining supremum of `affM ν χf A` is finite on `(0, 1.1/ν]`, i.e.
`s ↦ s^{-5/2} Σ_{j≤6} |(s∂_s)^j A^y(s)|` is bounded there, with `A^y = χ_f A` and `A ∈ 𝒜`.
Source 4955-4962 (`M(A)` is finite) and 5063-5079. -/
def AySumBdd (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ ν : ℝ, 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    BddAbove ((fun s => s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) '' Ioc 0 ((11 / 10) / ν))

theorem fac_frob_sq (A : Mat3) : frob A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold frob
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem fac_frob_nonneg (A : Mat3) : 0 ≤ frob A := Real.sqrt_nonneg _

theorem fac_frob_smul (c : ℝ) (A : Mat3) : frob (c • A) = |c| * frob A := by
  unfold frob
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem fac_frob_add_le (A B : Mat3) : frob (A + B) ≤ frob A + frob B := by
  have hc : ∑ i : Fin 3, ∑ j : Fin 3, A i j * B i j ≤ frob A * frob B := by
    have key : ∑ p : Fin 3 × Fin 3, A p.1 p.2 * B p.1 p.2 ≤
        Real.sqrt (∑ p : Fin 3 × Fin 3, A p.1 p.2 ^ 2) *
          Real.sqrt (∑ p : Fin 3 × Fin 3, B p.1 p.2 ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    unfold frob
    simpa [Fintype.sum_prod_type] using key
  have hsq : ∑ i, ∑ j, (A + B) i j ^ 2 ≤ (frob A + frob B) ^ 2 := by
    have h1 := fac_frob_sq A
    have h2 := fac_frob_sq B
    have e : (frob A + frob B) ^ 2 = frob A ^ 2 + 2 * (frob A * frob B) + frob B ^ 2 := by ring
    rw [e, h1, h2]
    simp only [Pi.add_apply, Fin.sum_univ_three] at hc ⊢
    nlinarith [hc]
  calc frob (A + B) = Real.sqrt (∑ i, ∑ j, (A + B) i j ^ 2) := rfl
    _ ≤ Real.sqrt ((frob A + frob B) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = frob A + frob B := Real.sqrt_sq (by positivity [fac_frob_nonneg A, fac_frob_nonneg B])

theorem fac_sDerivIter_one (A : ℝ → Mat3) : sDerivIter 1 A = sDeriv A := rfl

theorem fac_affSum_ge (A : ℝ → Mat3) (s : ℝ) :
    frob (sDerivIter 0 A s) + frob (sDerivIter 1 A s) ≤ affSum 6 A s := by
  have hp : ∑ j ∈ ({0, 1} : Finset ℕ), frob (sDerivIter j A s) =
      frob (sDerivIter 0 A s) + frob (sDerivIter 1 A s) :=
    Finset.sum_pair (by norm_num)
  have hs : ∑ j ∈ ({0, 1} : Finset ℕ), frob (sDerivIter j A s) ≤
      ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j A s) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp
    · intro i _ _
      exact fac_frob_nonneg _
  unfold affSum
  linarith

theorem fac_frob_Ay_le (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3)
    (hBdd : BddAbove ((fun s => s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χ A) s) ''
      Ioc 0 ((11 / 10) / ν)))
    (s : ℝ) (hs : 0 < s) (hsT : s ≤ (11 / 10) / ν) :
    frob (Ay ν χ A s) + frob (s • deriv (Ay ν χ A) s) ≤ s ^ (5 / 2 : ℝ) * affM ν χ A := by
  have hle : s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χ A) s ≤ affM ν χ A :=
    le_csSup hBdd ⟨s, ⟨hs, hsT⟩, rfl⟩
  have hge := fac_affSum_ge (Ay ν χ A) s
  have hr : s ^ (-(5 / 2 : ℝ)) = (s ^ (5 / 2 : ℝ))⁻¹ := Real.rpow_neg hs.le _
  have hpos : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have e0 : sDerivIter 0 (Ay ν χ A) s = Ay ν χ A s := rfl
  have e1 : sDerivIter 1 (Ay ν χ A) s = s • deriv (Ay ν χ A) s := rfl
  rw [e0, e1] at hge
  calc frob (Ay ν χ A s) + frob (s • deriv (Ay ν χ A) s) ≤ affSum 6 (Ay ν χ A) s := hge
    _ = s ^ (5 / 2 : ℝ) * (s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χ A) s) := by
        rw [hr, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    _ ≤ s ^ (5 / 2 : ℝ) * affM ν χ A := mul_le_mul_of_nonneg_left hle hpos.le

theorem fac_Bmat_eq (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (hs : 0 < s) :
    Bmat ν μ χ A s = s⁻¹ • (s • deriv (Ay ν χ A) s + μ • Ay ν χ A s) := by
  unfold Bmat
  funext i j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem fac_s52 (s : ℝ) (hs : 0 < s) : s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) * s := by
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hs, Real.rpow_one]

/-- `BmatBound` from the named leaf `AySumBdd`: `|B(s)| ≤ (1+μ) s^{3/2} M(A)`. -/
theorem bmatBound_of_aySumBdd (as : ℝ) (χf : ℝ → ℝ) (hB : AySumBdd as χf) : BmatBound as χf := by
  intro hχ ν μ hν hμ A hA s hs hsT
  have hbdd := hB hχ ν hν A hA
  have hk := fac_frob_Ay_le ν χf A hbdd s hs hsT
  have hμ1 : 0 ≤ 1 + μ := by linarith
  have h1 := fac_frob_add_le (s • deriv (Ay ν χf A) s) (μ • Ay ν χf A s)
  rw [fac_frob_smul μ (Ay ν χf A s), abs_of_nonneg hμ] at h1
  have hk2 : (1 + μ) * (frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s)) ≤
      (1 + μ) * (s ^ (5 / 2 : ℝ) * affM ν χf A) := mul_le_mul_of_nonneg_left hk hμ1
  have hnn1 : 0 ≤ μ * frob (Ay ν χf A s) := mul_nonneg hμ (fac_frob_nonneg _)
  have hnn2 : 0 ≤ frob (s • deriv (Ay ν χf A) s) := fac_frob_nonneg _
  have hnn3 : 0 ≤ frob (Ay ν χf A s) := fac_frob_nonneg _
  have hB1 : frob (s • deriv (Ay ν χf A) s + μ • Ay ν χf A s) ≤
      (1 + μ) * (s ^ (5 / 2 : ℝ) * affM ν χf A) := by
    nlinarith [h1, hk2, hnn1, hnn2, hnn3]
  have hinv : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
  rw [fac_Bmat_eq ν μ χf A s hs, fac_frob_smul, abs_of_pos (inv_pos.2 hs)]
  calc s⁻¹ * frob (s • deriv (Ay ν χf A) s + μ • Ay ν χf A s)
      ≤ s⁻¹ * ((1 + μ) * (s ^ (5 / 2 : ℝ) * affM ν χf A)) :=
        mul_le_mul_of_nonneg_left hB1 hinv
    _ = (1 + μ) * s ^ (3 / 2 : ℝ) * affM ν χf A := by
        rw [fac_s52 s hs]
        field_simp

/-- `PartIII-b:C/inst/9/2`: the leaf `AySumBdd` is discharged by the two environment theorems. -/
theorem bmatBound (as : ℝ) (χf : ℝ → ℝ) : BmatBound as χf :=
  bmatBound_of_aySumBdd as χf (aySumBdd_of sDerivIterDiffOn sDerivIterLeibniz as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
