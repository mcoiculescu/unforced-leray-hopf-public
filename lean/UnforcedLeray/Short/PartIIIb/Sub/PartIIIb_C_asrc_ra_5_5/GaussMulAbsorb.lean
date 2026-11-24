import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5

/-!
# `PartIII-b:C/asrc/ra/5/5` : absorption of polynomial growth into the Gaussian (source 4978)

Elementary estimates used by `GaussMulHbd`:
* `(1+t)^M e^{-c t} ≤ L^M` for `t ≥ 0` (with `L = 1 + M/c`);
* for `|η| ≤ R`, `(1+|x|²)^M e^{-|x|²/b} ≤ C e^{-q²/(2b)}` with `x = (q,η)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma gaussMul_polyExp (M : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ M * Real.exp (-c * t) ≤ C := by
  have hM : (0 : ℝ) ≤ (M : ℝ) / c := div_nonneg (Nat.cast_nonneg M) hc.le
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 1 + (M : ℝ) / c := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  have hL : 0 < L := by linarith
  have hL0 : L ≠ 0 := hL.ne'
  have hML : (M : ℝ) ≤ c * L := by
    rw [hLdef, mul_add, mul_one, mul_div_cancel₀ _ hc.ne']
    linarith
  refine ⟨L ^ M, pow_nonneg hL.le M, fun t ht => ?_⟩
  have h2 : t / L + 1 ≤ Real.exp (t / L) := by
    linarith [Real.add_one_le_exp (t / L)]
  have h3 : L * (t / L) = t := by field_simp
  have h4 : L * (t / L + 1) ≤ L * Real.exp (t / L) :=
    mul_le_mul_of_nonneg_left h2 hL.le
  have h5 : 1 + t ≤ L * Real.exp (t / L) := by nlinarith
  have h6 : (1 + t) ^ M ≤ (L * Real.exp (t / L)) ^ M :=
    pow_le_pow_left₀ (by linarith) h5 M
  have h7 : (L * Real.exp (t / L)) ^ M = L ^ M * Real.exp ((M : ℝ) * (t / L)) := by
    rw [mul_pow, Real.exp_nat_mul]
  have h8 : (M : ℝ) * (t / L) ≤ c * t := by
    rw [← mul_div_assoc, div_le_iff₀ hL]
    nlinarith [mul_nonneg ht (sub_nonneg.2 hML)]
  calc (1 + t) ^ M * Real.exp (-c * t)
      ≤ (L ^ M * Real.exp ((M : ℝ) * (t / L))) * Real.exp (-c * t) := by
        rw [← h7]
        exact mul_le_mul_of_nonneg_right h6 (Real.exp_nonneg _)
    _ = L ^ M * Real.exp ((M : ℝ) * (t / L) + -c * t) := by
        rw [Real.exp_add]
        ring
    _ ≤ L ^ M * 1 := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hL.le M)
        apply Real.exp_le_one_iff.2
        linarith
    _ = L ^ M := mul_one _

lemma gaussMul_absorb (M : ℕ) (R b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q η : ℝ, η ^ 2 ≤ R ^ 2 →
      (1 + sq2 (q, η)) ^ M * Real.exp (-(sq2 (q, η)) / b)
        ≤ C * Real.exp (-(1 / (2 * b)) * q ^ 2) := by
  have hc : 0 < 1 / (2 * b) := by positivity
  obtain ⟨L0, hL0, hpe⟩ := gaussMul_polyExp M hc
  refine ⟨(1 + R ^ 2) ^ M * L0, mul_nonneg (by positivity) hL0, fun q η hη => ?_⟩
  have hb0 : b ≠ 0 := hb.ne'
  have hX : sq2 (q, η) = q ^ 2 + η ^ 2 := by simp [sq2]
  rw [hX]
  have hle1 : 1 + (q ^ 2 + η ^ 2) ≤ (1 + R ^ 2) * (1 + q ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg R) (sq_nonneg q)]
  have hpow : (1 + (q ^ 2 + η ^ 2)) ^ M ≤ ((1 + R ^ 2) * (1 + q ^ 2)) ^ M :=
    pow_le_pow_left₀ (by positivity) hle1 M
  have hdiv : -(q ^ 2 + η ^ 2) / b ≤ -(q ^ 2) / b := by
    apply div_le_div_of_nonneg_right _ hb.le
    nlinarith [sq_nonneg η]
  have hexp : Real.exp (-(q ^ 2 + η ^ 2) / b) ≤ Real.exp (-(q ^ 2) / b) :=
    Real.exp_le_exp.2 hdiv
  have hsplit : Real.exp (-(q ^ 2) / b)
      = Real.exp (-(1 / (2 * b)) * q ^ 2) * Real.exp (-(1 / (2 * b)) * q ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hpe' := hpe (q ^ 2) (sq_nonneg q)
  have hE : 0 ≤ Real.exp (-(1 / (2 * b)) * q ^ 2) := Real.exp_nonneg _
  have hR : 0 ≤ (1 + R ^ 2) ^ M := by positivity
  calc (1 + (q ^ 2 + η ^ 2)) ^ M * Real.exp (-(q ^ 2 + η ^ 2) / b)
      ≤ ((1 + R ^ 2) * (1 + q ^ 2)) ^ M * Real.exp (-(q ^ 2) / b) :=
        mul_le_mul hpow hexp (Real.exp_nonneg _) (by positivity)
    _ = ((1 + R ^ 2) ^ M * Real.exp (-(1 / (2 * b)) * q ^ 2))
          * ((1 + q ^ 2) ^ M * Real.exp (-(1 / (2 * b)) * q ^ 2)) := by
        rw [mul_pow, hsplit]
        ring
    _ ≤ ((1 + R ^ 2) ^ M * Real.exp (-(1 / (2 * b)) * q ^ 2)) * L0 :=
        mul_le_mul_of_nonneg_left hpe' (mul_nonneg hR hE)
    _ = (1 + R ^ 2) ^ M * L0 * Real.exp (-(1 / (2 * b)) * q ^ 2) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
