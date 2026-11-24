import UnforcedLeray.Short.PartIIa.Calc.JetClass
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ExpPowAbsorb

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

/-- **Exponential smallness beats every power** (`WAbsorb`, lines 439-446). -/
theorem wAbsorb : WAbsorb := by
  intro a F hF
  intro ρ m hρ
  obtain ⟨C, d, κ, ν₀, hκ, hν₀, H⟩ := hF ρ m hρ
  obtain ⟨C₁, N₁, hC₁, H₁⟩ := expPowAbsorb κ ⌈max a 0⌉₊ hκ
  refine ⟨C * C₁, d + N₁, ν₀, hν₀, ?_⟩
  intro ν hν hνle tr htr x hx
  have hc : 0 < ν ^ (-ρ) := rpow_neg_pos hν
  have hHν := H ν hν hνle tr htr
  have hs1 : (1 : ℝ) ≤ x.2.2 := hx
  have hs0 : (0 : ℝ) ≤ x.2.2 := by linarith
  show (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| ≤
    polyConst (C * C₁) (d + N₁) ν (ν ^ (-ρ)) * x.2.2 ^ (-a)
  have hbound := hHν x hx
  have hPnn : 0 ≤ polyConst C d ν (ν ^ (-ρ)) := ExpBound.nonneg hHν
  have hw := weight_nonneg m hx
  have hXnn : 0 ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| :=
    mul_nonneg hw (abs_nonneg _)
  have hsa : x.2.2 ^ a ≤ x.2.2 ^ ((⌈max a 0⌉₊ : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_trans (le_max_left a 0) (Nat.le_ceil _))
  have hE := H₁ ν (ν ^ (-ρ)) x.2.2 hν hc hs0
  have hE2 : Real.exp (-(κ / 2 * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    have : 0 ≤ κ / 2 * ν * x.2.2 / (ν ^ (-ρ)) ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (by linarith) hν.le) hs0) (sq_nonneg _)
    linarith
  have hQ : 0 ≤ polyConst C₁ N₁ ν (ν ^ (-ρ)) := by
    unfold polyConst
    apply mul_nonneg hC₁
    apply pow_nonneg
    have := inv_pos.2 hν
    linarith
  have hfin : (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| * x.2.2 ^ a ≤
      polyConst (C * C₁) (d + N₁) ν (ν ^ (-ρ)) := by
    have e1 : (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| * x.2.2 ^ a ≤
        (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| * x.2.2 ^ ((⌈max a 0⌉₊ : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hsa hXnn
    have e2 : (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| * x.2.2 ^ ((⌈max a 0⌉₊ : ℕ) : ℝ)
        ≤ polyConst C d ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) *
          x.2.2 ^ ((⌈max a 0⌉₊ : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hs0 _)
    have e3 : polyConst C d ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) *
          x.2.2 ^ ((⌈max a 0⌉₊ : ℕ) : ℝ) =
        polyConst C d ν (ν ^ (-ρ)) *
          (x.2.2 ^ ((⌈max a 0⌉₊ : ℕ) : ℝ) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))) := by
      ring
    have e4 : x.2.2 ^ ((⌈max a 0⌉₊ : ℕ) : ℝ) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) ≤
        polyConst C₁ N₁ ν (ν ^ (-ρ)) * Real.exp (-(κ / 2 * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) := by
      rw [Real.rpow_natCast]
      exact hE
    have e5 : polyConst C₁ N₁ ν (ν ^ (-ρ)) * Real.exp (-(κ / 2 * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) ≤
        polyConst C₁ N₁ ν (ν ^ (-ρ)) := mul_le_of_le_one_right hQ hE2
    have e6 : polyConst C d ν (ν ^ (-ρ)) *
          (x.2.2 ^ ((⌈max a 0⌉₊ : ℕ) : ℝ) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))) ≤
        polyConst C d ν (ν ^ (-ρ)) * polyConst C₁ N₁ ν (ν ^ (-ρ)) :=
      mul_le_mul_of_nonneg_left (e4.trans e5) hPnn
    have e7 : polyConst C d ν (ν ^ (-ρ)) * polyConst C₁ N₁ ν (ν ^ (-ρ)) =
        polyConst (C * C₁) (d + N₁) ν (ν ^ (-ρ)) := by
      unfold polyConst
      rw [pow_add]
      ring
    calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| * x.2.2 ^ a
        ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| * x.2.2 ^ ((⌈max a 0⌉₊ : ℕ) : ℝ) := e1
      _ ≤ polyConst C d ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) *
          x.2.2 ^ ((⌈max a 0⌉₊ : ℕ) : ℝ) := e2
      _ = polyConst C d ν (ν ^ (-ρ)) *
          (x.2.2 ^ ((⌈max a 0⌉₊ : ℕ) : ℝ) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))) := e3
      _ ≤ polyConst C d ν (ν ^ (-ρ)) * polyConst C₁ N₁ ν (ν ^ (-ρ)) := e6
      _ = polyConst (C * C₁) (d + N₁) ν (ν ^ (-ρ)) := e7
  have hinv : x.2.2 ^ a * x.2.2 ^ (-a) = 1 := by
    rw [← Real.rpow_add (by linarith : (0 : ℝ) < x.2.2)]
    simp
  calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x|
      = ((1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| * x.2.2 ^ a) * x.2.2 ^ (-a) := by
        rw [mul_assoc, hinv, mul_one]
    _ ≤ polyConst (C * C₁) (d + N₁) ν (ν ^ (-ρ)) * x.2.2 ^ (-a) :=
        mul_le_mul_of_nonneg_right hfin (Real.rpow_nonneg hs0 _)

end UnforcedLeray.Short.PartIIa.Jet
