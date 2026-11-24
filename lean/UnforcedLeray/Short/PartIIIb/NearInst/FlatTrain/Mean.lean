import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Defs

/-!
# The mean part of the flat train bound (source 2722-2724)

Proves `flatMeanBound_of : MeanVelNorm → MeanStreamDerivBound → FlatMeanBound` from
`Defs.lean`. Pure real analysis: the transverse weight is at most `2^n (1 + η^{2n}/(1+s)^n)`
(`transWeight_le_two_pow`), the velocity is the transverse derivative of the mean stream
(`MeanVelNorm`), and the weighted derivative bounds (`MeanStreamDerivBound`) at `m = 0` and
`m = 2n` give `|∂_η S| ≤ A (1+s)^{-1}` and `η^{2n}|∂_η S| ≤ B (1+s)^{n-1}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete

/-- Pure algebra: the weighted mean velocity bound from the two pointwise estimates. -/
theorem flatMeanBound_step_aux {s W d x A B : ℝ} {n : ℕ} (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hW : W ≤ 2 ^ n * (1 + x / (1 + s) ^ n))
    (h0 : d ≤ A * (1 + s)⁻¹)
    (h1 : x * d ≤ B * (1 + s) ^ n * (1 + s)⁻¹) :
    Real.sqrt s * W * d ≤ 2 ^ n * (A + B) := by
  have hpos : 0 < 1 + s := by linarith
  have hsq : Real.sqrt s * (1 + s)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hpos]
    nlinarith [Real.sq_sqrt hs, sq_nonneg (Real.sqrt s - 1 / 2), Real.sqrt_nonneg s]
  have ht : 0 < (1 + s) ^ n := pow_pos hpos n
  have hq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hsd : Real.sqrt s * W * d ≤ Real.sqrt s * (2 ^ n * (1 + x / (1 + s) ^ n)) * d :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hq) hd
  have hexp : Real.sqrt s * (2 ^ n * (1 + x / (1 + s) ^ n)) * d
      = 2 ^ n * (Real.sqrt s * d + Real.sqrt s * (x * d) / (1 + s) ^ n) := by
    ring
  have hA1 : Real.sqrt s * d ≤ A := by
    calc Real.sqrt s * d ≤ Real.sqrt s * (A * (1 + s)⁻¹) := mul_le_mul_of_nonneg_left h0 hq
      _ = A * (Real.sqrt s * (1 + s)⁻¹) := by ring
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hsq hA
      _ = A := mul_one A
  have hB1 : Real.sqrt s * (x * d) / (1 + s) ^ n ≤ B := by
    rw [div_le_iff₀ ht]
    calc Real.sqrt s * (x * d) ≤ Real.sqrt s * (B * (1 + s) ^ n * (1 + s)⁻¹) :=
          mul_le_mul_of_nonneg_left h1 hq
      _ = B * (Real.sqrt s * (1 + s)⁻¹) * (1 + s) ^ n := by ring
      _ ≤ B * 1 * (1 + s) ^ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hB) ht.le
      _ = B * (1 + s) ^ n := by ring
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  calc Real.sqrt s * W * d
      ≤ Real.sqrt s * (2 ^ n * (1 + x / (1 + s) ^ n)) * d := hsd
    _ = 2 ^ n * (Real.sqrt s * d + Real.sqrt s * (x * d) / (1 + s) ^ n) := hexp
    _ ≤ 2 ^ n * (A + B) := mul_le_mul_of_nonneg_left (add_le_add hA1 hB1) h2n

/-- **The mean part of the flat train bound, from the mean velocity identity and the weighted
derivative bounds** (source 2722-2724). -/
theorem flatMeanBound_of (h1 : MeanVelNorm) (h2 : MeanStreamDerivBound) : FlatMeanBound := by
  intro mZ hmZ
  obtain ⟨C₀, k₀, ν₀, hν₀, hb₀⟩ := h2 0
  obtain ⟨C₁, k₁, ν₁, hν₁, hb₁⟩ := h2 (2 * ⌈mZ / 2⌉₊)
  refine ⟨2 ^ ⌈mZ / 2⌉₊ * (max C₀ 0 + max C₁ 0), max k₀ k₁, min (min ν₀ ν₁) 1,
    lt_min (lt_min hν₀ hν₁) one_pos, ?_⟩
  intro ν hν c hc tr hbuc p hp
  obtain ⟨s, q, η⟩ := p
  dsimp only at hp ⊢
  have hs : 0 < s := hp
  have hν0 : 0 < ν := hν.1
  have hνa : ν ≤ ν₀ := hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνb : ν ≤ ν₁ := hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have hc0 : 0 < c := by rw [hc]; positivity
  have hmean := h1 ν c hν0 hc0 tr hbuc s hs η
  have hF := hb₀ ν ⟨hν0, hνa⟩ c hc tr hbuc s hs η
  have hM := hb₁ ν ⟨hν0, hνb⟩ c hc tr hbuc s hs η
  have e0 : ((((0 : ℕ) : ℝ) - 2) / 2) = -1 := by norm_num
  rw [pow_zero, one_mul, e0, Real.rpow_neg_one] at hF
  have hpos : (0 : ℝ) < 1 + s := by linarith
  have e1 : ((((2 * ⌈mZ / 2⌉₊ : ℕ) : ℝ) - 2) / 2) = ((⌈mZ / 2⌉₊ : ℕ) : ℝ) - 1 := by
    push_cast; ring
  rw [e1, Real.rpow_sub_one hpos.ne', Real.rpow_natCast,
    Even.pow_abs (even_two_mul _)] at hM
  have hiv : 0 ≤ ν⁻¹ ^ max k₀ k₁ := pow_nonneg (inv_nonneg.mpr hν0.le) _
  have hA : 0 ≤ max C₀ 0 * ν⁻¹ ^ max k₀ k₁ := mul_nonneg (le_max_right _ _) hiv
  have hB : 0 ≤ max C₁ 0 * ν⁻¹ ^ max k₀ k₁ := mul_nonneg (le_max_right _ _) hiv
  have hF2 : |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| ≤
      max C₀ 0 * ν⁻¹ ^ max k₀ k₁ * (1 + s)⁻¹ :=
    hF.trans (mul_le_mul_of_nonneg_right
      (mul_inv_pow_le_max hν0 hν1 (le_max_left k₀ k₁)) (inv_nonneg.mpr hpos.le))
  have hCν : C₁ * ν⁻¹ ^ k₁ ≤ max C₁ 0 * ν⁻¹ ^ max k₀ k₁ :=
    mul_inv_pow_le_max hν0 hν1 (le_max_right k₀ k₁)
  have hdiv : C₁ * ν⁻¹ ^ k₁ * ((1 + s) ^ ⌈mZ / 2⌉₊ / (1 + s))
      ≤ max C₁ 0 * ν⁻¹ ^ max k₀ k₁ * (1 + s) ^ ⌈mZ / 2⌉₊ * (1 + s)⁻¹ := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCν (pow_nonneg hpos.le ⌈mZ / 2⌉₊)) (inv_nonneg.mpr hpos.le)
    calc C₁ * ν⁻¹ ^ k₁ * ((1 + s) ^ ⌈mZ / 2⌉₊ / (1 + s))
        = C₁ * ν⁻¹ ^ k₁ * (1 + s) ^ ⌈mZ / 2⌉₊ * (1 + s)⁻¹ := by ring
      _ ≤ max C₁ 0 * ν⁻¹ ^ max k₀ k₁ * (1 + s) ^ ⌈mZ / 2⌉₊ * (1 + s)⁻¹ := h
  have hM2 : η ^ (2 * ⌈mZ / 2⌉₊) * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η|
      ≤ max C₁ 0 * ν⁻¹ ^ max k₀ k₁ * (1 + s) ^ ⌈mZ / 2⌉₊ * (1 + s)⁻¹ :=
    le_trans hM hdiv
  have hd0 : 0 ≤ |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| :=
    abs_nonneg _
  rw [hmean]
  have hstep := flatMeanBound_step_aux (n := ⌈mZ / 2⌉₊) hs.le hd0 hA hB
    (transWeight_le_two_pow mZ hs.le q η) hF2 hM2
  exact hstep.trans (le_of_eq (by ring))

end UnforcedLeray.Short.PartIIIb.NearInst
