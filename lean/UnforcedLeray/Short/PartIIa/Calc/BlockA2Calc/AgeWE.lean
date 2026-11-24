import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc

/-!
# Part II-a, block `A₂`, task `PartII-a:R02/12/4`: an age derivative of an exponentially small family

Source: `the November 2 reference manuscript`, lines 439-446.
From `2s∂_s f = Kf - η∂_η f` and `s ≥ 1`, `|η| ≤ 2s w` with `w = 1 + η²/s`, so
`w^m |∂_s f| ≤ w^m |Kf| + w^(m+1) |∂_η f|`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet.A2

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- Pointwise age estimate (`s = x.2.2 ≥ 1`, `η = x.2.1`, `w = 1 + η²/s`):
`w^m |∂_s f| ≤ w^m |Kf| + w^(m+1) |∂_η f|`. -/
theorem ha1_age_pt (f : ProfilePoint → ℝ) (m : ℕ) (x : ProfilePoint) (hx : 1 ≤ x.2.2) :
    (1 + x.2.1 ^ 2 / x.2.2) ^ m * |partialAge f x| ≤
      (1 + x.2.1 ^ 2 / x.2.2) ^ m * |ageOperator f x|
        + (1 + x.2.1 ^ 2 / x.2.2) ^ (m + 1) * |partialEta f x| := by
  have hs0 : (0 : ℝ) < x.2.2 := by linarith
  have hsne : x.2.2 ≠ 0 := hs0.ne'
  have hpos : (0 : ℝ) < 2 * x.2.2 := by linarith
  have hw0 : (0 : ℝ) ≤ 1 + x.2.1 ^ 2 / x.2.2 := by
    have := div_nonneg (sq_nonneg x.2.1) hs0.le
    linarith
  have hAs : partialAge f x * (2 * x.2.2) = ageOperator f x - x.2.1 * partialEta f x := by
    unfold ageOperator
    ring
  have hab : |partialAge f x| * (2 * x.2.2) = |ageOperator f x - x.2.1 * partialEta f x| := by
    have h := congrArg abs hAs
    rwa [abs_mul, abs_of_pos hpos] at h
  have hKE : |ageOperator f x - x.2.1 * partialEta f x|
      ≤ |ageOperator f x| + |x.2.1| * |partialEta f x| := by
    calc |ageOperator f x - x.2.1 * partialEta f x|
        ≤ |ageOperator f x| + |x.2.1 * partialEta f x| := abs_sub _ _
      _ = |ageOperator f x| + |x.2.1| * |partialEta f x| := by rw [abs_mul]
  have hw2 : |x.2.1| ≤ 2 * x.2.2 * (1 + x.2.1 ^ 2 / x.2.2) := by
    have e : 2 * x.2.2 * (1 + x.2.1 ^ 2 / x.2.2) = 2 * x.2.2 + 2 * x.2.1 ^ 2 := by
      field_simp
    rw [e]
    nlinarith [sq_abs x.2.1, abs_nonneg x.2.1, sq_nonneg (|x.2.1| - 1 / 4)]
  have hfin : |x.2.1| * |partialEta f x|
      ≤ (2 * x.2.2 * (1 + x.2.1 ^ 2 / x.2.2)) * |partialEta f x| :=
    mul_le_mul_of_nonneg_right hw2 (abs_nonneg _)
  have hK2 : |ageOperator f x| ≤ 2 * x.2.2 * |ageOperator f x| := by
    nlinarith [abs_nonneg (ageOperator f x)]
  have key : (2 * x.2.2) * |partialAge f x|
      ≤ (2 * x.2.2) * (|ageOperator f x| + (1 + x.2.1 ^ 2 / x.2.2) * |partialEta f x|) := by
    nlinarith [hab, hKE, hfin, hK2]
  have hA : |partialAge f x| ≤ |ageOperator f x| + (1 + x.2.1 ^ 2 / x.2.2) * |partialEta f x| :=
    le_of_mul_le_mul_left key hpos
  have hpow : (1 + x.2.1 ^ 2 / x.2.2) ^ (m + 1)
      = (1 + x.2.1 ^ 2 / x.2.2) ^ m * (1 + x.2.1 ^ 2 / x.2.2) := pow_succ _ _
  calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * |partialAge f x|
      ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m
          * (|ageOperator f x| + (1 + x.2.1 ^ 2 / x.2.2) * |partialEta f x|) :=
        mul_le_mul_of_nonneg_left hA (pow_nonneg hw0 m)
    _ = (1 + x.2.1 ^ 2 / x.2.2) ^ m * |ageOperator f x|
          + (1 + x.2.1 ^ 2 / x.2.2) ^ (m + 1) * |partialEta f x| := by
        rw [hpow]
        ring

/-- **An age derivative of an exponentially small family is exponentially small**
(task `PartII-a:R02/12/4`). -/
theorem ageWE : UnforcedLeray.Short.PartIIa.Jet.A2.AgeWE := by
  intro F hK hE ρ m hρ
  obtain ⟨C₁, d₁, κ₁, ν₁, hκ₁, hν₁, H₁⟩ := hK ρ m hρ
  obtain ⟨C₂, d₂, κ₂, ν₂, hκ₂, hν₂, H₂⟩ := hE ρ (m + 1) hρ
  refine ⟨max C₁ 0 + max C₂ 0, max d₁ d₂, min κ₁ κ₂, min ν₁ ν₂, lt_min hκ₁ hκ₂,
    lt_min hν₁ hν₂, ?_⟩
  intro ν hν hνle tr htr x hx
  have hc := rpow_neg_pos (ρ := ρ) hν
  have h1 := ExpBound.mono' hν hc (min_le_left κ₁ κ₂)
    (polyConst_le_max (C := C₁) hν hc (le_max_left d₁ d₂))
    (H₁ ν hν (hνle.trans (min_le_left _ _)) tr htr)
  have h2 := ExpBound.mono' hν hc (min_le_right κ₁ κ₂)
    (polyConst_le_max (C := C₂) hν hc (le_max_right d₁ d₂))
    (H₂ ν hν (hνle.trans (min_le_right _ _)) tr htr)
  have hK' : (1 + x.2.1 ^ 2 / x.2.2) ^ m * |ageOperator (F ν (ν ^ (-ρ)) tr) x|
      ≤ polyConst (max C₁ 0) (max d₁ d₂) ν (ν ^ (-ρ))
        * Real.exp (-(min κ₁ κ₂ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) :=
    h1 x hx
  have hE' : (1 + x.2.1 ^ 2 / x.2.2) ^ (m + 1) * |partialEta (F ν (ν ^ (-ρ)) tr) x|
      ≤ polyConst (max C₂ 0) (max d₁ d₂) ν (ν ^ (-ρ))
        * Real.exp (-(min κ₁ κ₂ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) :=
    h2 x hx
  have hP := ha1_age_pt (F ν (ν ^ (-ρ)) tr) m x hx
  show (1 + x.2.1 ^ 2 / x.2.2) ^ m * |partialAge (F ν (ν ^ (-ρ)) tr) x| ≤ _
  rw [polyConst_add, add_mul]
  exact hP.trans (add_le_add hK' hE')

end UnforcedLeray.Short.PartIIa.Jet.A2
