import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/17`: the fold sum of the phase weights

Source `the November 2 reference manuscript` (the fold of the task spec:
`l = e^{-mc/R} λ`, `Σ_m e^{-mc/R} ≤ 1 + R/c`; here `P = 2c/R`).  For `σ ∈ (0, P]`:
the index `n ≥ 1` gives a zero term; `n = 0` gives a term at most `√P/2`; the indices
`n = -(m+1)` give `σ + nP ≤ -mP ≤ 0`, so the term is at most `(√P/2) e^{-mP/2}`, and the
geometric sum `Σ_m e^{-mP/2} = (1 - e^{-P/2})⁻¹ ≤ 1 + 2/P` gives the total
`√P/2 + (√P/2)(1 + 2/P) = √P + 1/√P`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- The geometric bound `(1 - e^{-x})⁻¹ ≤ 1 + 1/x` for `x = P/2`, from `1 + x ≤ e^x`. -/
lemma omegaSum_geom (P : ℝ) (hP : 0 < P) :
    (1 - Real.exp (-(P / 2)))⁻¹ ≤ 1 + 2 / P := by
  have hrE : Real.exp (-(P / 2)) * Real.exp (P / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hE : P / 2 + 1 ≤ Real.exp (P / 2) := by
    have := Real.add_one_le_exp (P / 2)
    linarith
  have hE0 : 0 < Real.exp (P / 2) := Real.exp_pos _
  have hr1 : Real.exp (-(P / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h1r : 0 < 1 - Real.exp (-(P / 2)) := by linarith
  have hq' : 2 / P * (P / 2) = 1 := by field_simp
  have h2 : 0 ≤ (2 / P) * (Real.exp (P / 2) - (P / 2 + 1)) :=
    mul_nonneg (by positivity) (by linarith)
  have hid : Real.exp (P / 2) * (2 / P - Real.exp (-(P / 2)) * (1 + 2 / P)) =
      (2 / P) * (Real.exp (P / 2) - (P / 2 + 1)) := by
    linear_combination (-(1 + 2 / P)) * hrE + hq'
  have hX : 0 ≤ 2 / P - Real.exp (-(P / 2)) * (1 + 2 / P) :=
    (mul_nonneg_iff_of_pos_left hE0).1 (by rw [hid]; exact h2)
  rw [inv_eq_one_div, div_le_iff₀ h1r]
  have hexp : (1 + 2 / P) * (1 - Real.exp (-(P / 2))) - 1 =
      2 / P - Real.exp (-(P / 2)) * (1 + 2 / P) := by ring
  linarith

/-- The term at index `0`: `omega2 P σ ≤ P/4`, so its square root is at most `√P/2`. -/
lemma omegaSum_sqrt_zero (P σ : ℝ) (hP : 0 < P) :
    Real.sqrt (omega2 P σ) ≤ Real.sqrt P / 2 := by
  have hle : omega2 P σ ≤ P / 4 := by
    unfold omega2
    split_ifs
    · exact mul_le_of_le_one_right (by positivity) (min_le_left _ _)
    · positivity
  have hsq : (Real.sqrt P / 2) ^ 2 = P / 4 := by
    rw [div_pow, Real.sq_sqrt hP.le]
    ring
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [hsq]
  exact hle

/-- A negative index: `x ≤ -mP` gives `√(omega2 P x) ≤ (√P/2) (e^{-P/2})^m`. -/
lemma omegaSum_sqrt_neg (P x : ℝ) (m : ℕ) (hP : 0 < P) (hx : x ≤ -((m : ℝ) * P)) :
    Real.sqrt (omega2 P x) ≤ Real.sqrt P / 2 * (Real.exp (-(P / 2))) ^ m := by
  have hm : (0 : ℝ) ≤ (m : ℝ) * P := by positivity
  have hxP : x < P := by linarith
  have hom : omega2 P x ≤ P / 4 * Real.exp (-((m : ℝ) * P)) := by
    unfold omega2
    rw [if_pos hxP]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (min_le_right _ _).trans (Real.exp_le_exp.2 hx)
  have hpow : (Real.exp (-(P / 2))) ^ m = Real.exp (-((m : ℝ) * P) / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h2 : Real.exp (-((m : ℝ) * P) / 2) ^ 2 = Real.exp (-((m : ℝ) * P)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hB : 0 ≤ Real.sqrt P / 2 * (Real.exp (-(P / 2))) ^ m := by positivity
  rw [Real.sqrt_le_iff]
  refine ⟨hB, ?_⟩
  have hsq : (Real.sqrt P / 2 * (Real.exp (-(P / 2))) ^ m) ^ 2 =
      P / 4 * Real.exp (-((m : ℝ) * P)) := by
    rw [hpow, mul_pow, div_pow, Real.sq_sqrt hP.le, h2]
    ring
  rw [hsq]
  exact hom

/-- The summand of the fold sum, indexed by `n : ℤ`. -/
def omegaSumTerm (P σ : ℝ) (n : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (omega2 P (σ + n * P)))

/-- Indices `n ≥ 1` give zero terms when `σ > 0`. -/
lemma omegaSum_omega2_pos_index (P σ : ℝ) (n : ℤ) (hP : 0 < P) (hσ : 0 < σ)
    (hn : 1 ≤ n) : omega2 P (σ + n * P) = 0 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold omega2
  split_ifs with h
  · exfalso
    nlinarith [mul_nonneg (sub_nonneg.2 hn') hP.le]
  · rfl

/-- **The fold sum** (task spec: `l = e^{-mc/R}λ`, `Σ_m e^{-mc/R} ≤ 1 + R/c`): for `σ ∈ (0, P]`,
`Σ_n √omega2(σ + nP) ≤ √P + 1/√P`. -/
theorem omegaSum : OmegaSum := by
  intro P hP σ hσ
  obtain ⟨hσ0, hσP⟩ := hσ
  have hsum := tsum_of_nat_of_neg_add_one (f := omegaSumTerm P σ)
    ENNReal.summable ENNReal.summable
  refine le_trans (le_of_eq hsum) ?_
  -- the nonnegative indices
  have hA : ∑' n : ℕ, omegaSumTerm P σ (n : ℤ) ≤ ENNReal.ofReal (Real.sqrt P / 2) := by
    have hz : ∀ b : ℕ, b ≠ 0 → omegaSumTerm P σ (b : ℤ) = 0 := by
      intro b hb
      unfold omegaSumTerm
      rw [omegaSum_omega2_pos_index P σ (b : ℤ) hP hσ0 (by omega)]
      simp
    refine (tsum_eq_single 0 hz).trans_le ?_
    unfold omegaSumTerm
    have := ENNReal.ofReal_le_ofReal (omegaSum_sqrt_zero P σ hP)
    simpa using this
  -- the negative indices `n = -(m+1)`
  have hr0 : 0 < Real.exp (-(P / 2)) := Real.exp_pos _
  have hs0 : 0 ≤ Real.sqrt P / 2 := by positivity
  have hB1 : ∀ m : ℕ, omegaSumTerm P σ (-((m : ℤ) + 1)) ≤
      ENNReal.ofReal (Real.sqrt P / 2) * ENNReal.ofReal (Real.exp (-(P / 2))) ^ m := by
    intro m
    have hx : σ + ((-((m : ℤ) + 1) : ℤ) : ℝ) * P ≤ -((m : ℝ) * P) := by
      push_cast
      nlinarith
    unfold omegaSumTerm
    rw [← ENNReal.ofReal_pow hr0.le, ← ENNReal.ofReal_mul hs0]
    exact ENNReal.ofReal_le_ofReal (omegaSum_sqrt_neg P _ m hP hx)
  have h1r : 0 < 1 - Real.exp (-(P / 2)) := by
    have : Real.exp (-(P / 2)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hgeom : (1 - ENNReal.ofReal (Real.exp (-(P / 2))))⁻¹ ≤
      ENNReal.ofReal (1 + 2 / P) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hr0.le,
      ← ENNReal.ofReal_inv_of_pos h1r]
    exact ENNReal.ofReal_le_ofReal (omegaSum_geom P hP)
  have hBsum : ∑' n : ℕ, omegaSumTerm P σ (-((n : ℤ) + 1)) ≤
      ENNReal.ofReal (Real.sqrt P / 2) * (1 - ENNReal.ofReal (Real.exp (-(P / 2))))⁻¹ := by
    calc ∑' n : ℕ, omegaSumTerm P σ (-((n : ℤ) + 1))
        ≤ ∑' m : ℕ, ENNReal.ofReal (Real.sqrt P / 2) *
            ENNReal.ofReal (Real.exp (-(P / 2))) ^ m := ENNReal.tsum_le_tsum hB1
      _ = ENNReal.ofReal (Real.sqrt P / 2) *
            ∑' m : ℕ, ENNReal.ofReal (Real.exp (-(P / 2))) ^ m := ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (Real.sqrt P / 2) *
            (1 - ENNReal.ofReal (Real.exp (-(P / 2))))⁻¹ := by
        rw [ENNReal.tsum_geometric]
  -- the arithmetic of the constants
  have hsP : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP.le
  have hsqrt_pos : 0 < Real.sqrt P := Real.sqrt_pos.2 hP
  have hdiv : Real.sqrt P / P = 1 / Real.sqrt P := by
    rw [div_eq_div_iff hP.ne' hsqrt_pos.ne']
    linarith
  have hconst : Real.sqrt P / 2 + Real.sqrt P / 2 * (1 + 2 / P) =
      Real.sqrt P + 1 / Real.sqrt P := by
    rw [← hdiv]
    ring
  have hfinal : ENNReal.ofReal (Real.sqrt P / 2) +
      ENNReal.ofReal (Real.sqrt P / 2) * (1 - ENNReal.ofReal (Real.exp (-(P / 2))))⁻¹ ≤
      ENNReal.ofReal (Real.sqrt P + 1 / Real.sqrt P) := by
    calc ENNReal.ofReal (Real.sqrt P / 2) +
          ENNReal.ofReal (Real.sqrt P / 2) * (1 - ENNReal.ofReal (Real.exp (-(P / 2))))⁻¹
        ≤ ENNReal.ofReal (Real.sqrt P / 2) +
          ENNReal.ofReal (Real.sqrt P / 2) * ENNReal.ofReal (1 + 2 / P) :=
          by gcongr
      _ = ENNReal.ofReal (Real.sqrt P / 2 + Real.sqrt P / 2 * (1 + 2 / P)) := by
          rw [ENNReal.ofReal_add hs0 (mul_nonneg hs0 (by positivity)),
            ENNReal.ofReal_mul hs0]
      _ = ENNReal.ofReal (Real.sqrt P + 1 / Real.sqrt P) := by rw [hconst]
  exact (add_le_add hA hBsum).trans hfinal

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
