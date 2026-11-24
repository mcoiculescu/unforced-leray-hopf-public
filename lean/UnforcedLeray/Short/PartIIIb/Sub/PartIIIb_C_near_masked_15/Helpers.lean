import UnforcedLeray.Short.PartIIIb.NearInst.Chart
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1
import UnforcedLeray.Short.PartIIIa.SeparatedKernels

/-!
# Helpers for the masked-lift leaves `MaskedLiftSource` and `MaskedLiftMoment`

Pure algebra on `NearInst.chartOf`, `NearInst.cylFrame`, `NearInst.nsSym`, `NearInst.cartLift`
used by `L1.lean` and `L2.lean` (source 3604-3646, 3905-3912, 4155-4156).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.H15

open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.NearInst

lemma nsSym_zero' : nsSym (0 : Ten3) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nsSym, symRZ]

lemma abs_div_hRad_le (a : ℝ) (z : Space) (ha : |a| ≤ hRad z) : |a / hRad z| ≤ 1 := by
  by_cases h0 : hRad z = 0
  · rw [h0, div_zero, abs_zero]; norm_num
  · have hnn : 0 ≤ hRad z := Real.sqrt_nonneg _
    have hpos : 0 < hRad z := lt_of_le_of_ne hnn (Ne.symm h0)
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact ha

lemma cylFrame_abs_le (z : Space) (i j : Fin 3) : |cylFrame z i j| ≤ 1 := by
  have h0 : |z 0| ≤ hRad z := by
    unfold hRad; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (z 1)])
  have h1 : |z 1| ≤ hRad z := by
    unfold hRad; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (z 0)])
  fin_cases i <;> fin_cases j <;>
    simp [cylFrame, abs_div_hRad_le, abs_neg, h0, h1]

lemma mul3_abs_le (A B : Matrix (Fin 3) (Fin 3) ℝ) (a b : ℝ) (ha : ∀ i j, |A i j| ≤ a)
    (hb : ∀ i j, |B i j| ≤ b) (ha0 : 0 ≤ a) (i j : Fin 3) :
    |(A * B) i j| ≤ 3 * (a * b) := by
  have key : ∀ k : Fin 3, |A i k * B k j| ≤ a * b := fun k => by
    rw [abs_mul]
    exact mul_le_mul (ha i k) (hb k j) (abs_nonneg _) ha0
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  calc |A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j|
      ≤ |A i 0 * B 0 j| + |A i 1 * B 1 j| + |A i 2 * B 2 j| := abs_add_three _ _ _
    _ ≤ a * b + a * b + a * b := by linarith [key 0, key 1, key 2]
    _ = 3 * (a * b) := by ring

lemma cylMul_abs_le (z : Space) (N : Matrix (Fin 3) (Fin 3) ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hN : ∀ i j, |N i j| ≤ K) (i j : Fin 3) :
    |(cylFrame z * N * (cylFrame z).transpose) i j| ≤ 9 * K := by
  have hA : ∀ i j, |(cylFrame z * N) i j| ≤ 3 * (1 * K) :=
    fun i j => mul3_abs_le _ _ 1 K (fun a b => cylFrame_abs_le z a b) hN zero_le_one i j
  have hT : ∀ i j, |(cylFrame z).transpose i j| ≤ 1 := fun i j => by
    rw [Matrix.transpose_apply]; exact cylFrame_abs_le z j i
  have h := mul3_abs_le _ _ (3 * (1 * K)) 1 hA hT (by linarith) i j
  linarith

lemma abs_nsSym_le (T : Ten3) (B : ℝ) (hT : ‖T‖ ≤ B) (i j : Fin 3) : |nsSym T i j| ≤ B := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hT
  have hc : ∀ ab : Fin 3 × Fin 3, |T ab| ≤ B := fun ab => by
    have h := PiLp.norm_apply_le T ab
    rw [Real.norm_eq_abs] at h
    linarith
  have hsym : |symRZ T| ≤ B := by
    have h1 := abs_le.1 (hc (0, 2))
    have h2 := abs_le.1 (hc (2, 0))
    unfold symRZ
    exact abs_le.2 ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
  fin_cases i <;> fin_cases j <;> simp [nsSym, hsym, hc, hB0]

lemma abs_smul_nsSym_le (a : ℝ) (T : Ten3) (S B : ℝ) (ha : |a| ≤ S) (hT : ‖T‖ ≤ B)
    (hS : 0 ≤ S) (_hB : 0 ≤ B) (i j : Fin 3) :
    |(a • nsSym T) i j| ≤ S * B := by
  rw [Matrix.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul ha (abs_nsSym_le T B hT i j) (abs_nonneg _) hS

lemma abs_cartLift_le (R c : ℝ) (f : Chart → Ten3) (τ : ℝ) (z : Space) (S B : ℝ)
    (hS : 0 ≤ S) (hB : 0 ≤ B) (hfB : ‖f (chartOf R c z τ)‖ ≤ B)
    (ha : |(chartOf R c z τ).1| ≤ S) (i j : Fin 3) :
    |cartLift R c f τ z i j| ≤ 9 * (S * B) := by
  unfold cartLift
  exact cylMul_abs_le z _ (S * B) (mul_nonneg hS hB)
    (fun i j => abs_smul_nsSym_le _ _ S B ha hfB hS hB i j) i j

lemma tensorNorm_le_of_entries (M : Matrix (Fin 3) (Fin 3) ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ i j, |M i j| ≤ K) : IIIa.tensorNorm M ≤ 3 * K := by
  unfold IIIa.tensorNorm
  have hsq : ∀ i j, M i j ^ 2 ≤ K ^ 2 := fun i j => by
    nlinarith [abs_nonneg (M i j), sq_abs (M i j), h i j]
  calc Real.sqrt (∑ i, ∑ j, M i j ^ 2) ≤ Real.sqrt ((3 * K) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Fin.sum_univ_three]
        nlinarith [hsq 0 0, hsq 0 1, hsq 0 2, hsq 1 0, hsq 1 1, hsq 1 2, hsq 2 0, hsq 2 1, hsq 2 2]
    _ = 3 * K := Real.sqrt_sq (by linarith)

lemma chartOf_period (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (z : Space) (τ : ℝ) :
    chartOf R c z (τ + 2 * c / R) = chartOf R c z τ := by
  have hR0 : R ≠ 0 := hR.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have e1 : R * (τ + 2 * c / R) / 2 = R * τ / 2 + c := by
    field_simp
  have e2 : (R * Real.log (hRad z / R) + R * (τ + 2 * c / R) / 2) / c + 1 / 2
      = (R * Real.log (hRad z / R) + R * τ / 2) / c + 1 / 2 + 1 := by
    rw [e1]
    field_simp
    ring
  unfold chartOf
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  rw [e2, Int.floor_add_one, e1]
  push_cast
  ring

lemma mem_closedBall_of_sumsq (z : Space) (r : ℝ) (h : z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≤ r) :
    z ∈ Metric.closedBall (0 : Space) (Real.sqrt r) := by
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  exact Real.sqrt_le_sqrt h

lemma sumsq_le_of_band (R L s1 : ℝ) (hR : 0 < R) (hs1 : 0 < s1) (z : Space)
    (hage : s1 ≤ R ^ 2 / hRad z ^ 2) (heta : |R * z 2 / hRad z| ≤ L) :
    z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≤ (R ^ 2 + L ^ 2) / s1 := by
  have hx : hRad z ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
    unfold hRad
    exact Real.sq_sqrt (by positivity)
  have hpos : 0 < hRad z ^ 2 := by
    rcases (sq_nonneg (hRad z)).eq_or_lt with h | h
    · rw [← h, div_zero] at hage
      linarith
    · exact h
  have hb : s1 * hRad z ^ 2 ≤ R ^ 2 := (le_div_iff₀ hpos).1 hage
  have ha : R ^ 2 * z 2 ^ 2 ≤ L ^ 2 * hRad z ^ 2 := by
    have h1 : (R * z 2 / hRad z) ^ 2 ≤ L ^ 2 := by
      nlinarith [abs_nonneg (R * z 2 / hRad z), sq_abs (R * z 2 / hRad z)]
    rw [div_pow, mul_pow, div_le_iff₀ hpos] at h1
    exact h1
  have hA : R ^ 2 * (s1 * z 2 ^ 2) ≤ R ^ 2 * L ^ 2 := by
    calc R ^ 2 * (s1 * z 2 ^ 2) = s1 * (R ^ 2 * z 2 ^ 2) := by ring
      _ ≤ s1 * (L ^ 2 * hRad z ^ 2) := mul_le_mul_of_nonneg_left ha hs1.le
      _ = L ^ 2 * (s1 * hRad z ^ 2) := by ring
      _ ≤ L ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left hb (sq_nonneg L)
      _ = R ^ 2 * L ^ 2 := by ring
  have hz2 : s1 * z 2 ^ 2 ≤ L ^ 2 := le_of_mul_le_mul_left hA (pow_pos hR 2)
  have hxs : s1 * (z 0 ^ 2 + z 1 ^ 2) ≤ R ^ 2 := by
    rw [← hx]; exact hb
  rw [le_div_iff₀ hs1]
  nlinarith [hxs, hz2]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.H15
