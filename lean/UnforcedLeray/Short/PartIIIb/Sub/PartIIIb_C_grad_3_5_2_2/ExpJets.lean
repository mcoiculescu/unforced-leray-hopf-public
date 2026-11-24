import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2_2.ArgLower
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2_2.ArgJets
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2_2.ExpComp

/-!
# `PartIII-b:C/grad/3/5/2/2` task 1: jet bounds of the Gaussian factor `exp(-|x_j|²/(4a))`

Source `the November 2 reference manuscript`
5063-5079, 4974-4980.  Combine the lower exponent bound (`psijArgLower`, task 1a), the jet bound
of the exponent (`psijArgJets`, task 1b) and the Faà di Bruno bound for `exp(-f)` (`expNegCompJets`,
task 1c).  For each `j`, `T_j = c j² - K` and `D_j = D (1+|j|)²`; the bound
`k! e^{-T_j} D_j^k ≤ 6 e^K D³ (1+|j|)⁶ e^{-c j²}` holds for `k ≤ 3` since `D_j ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psijExpJets : PsijExpJets := by
  intro ν hν U hUo _hconv hcl hbd
  obtain ⟨c, K, hc, hlow⟩ := psijArgLower ν hν U hcl hbd
  obtain ⟨D, hD1, hjet⟩ := psijArgJets ν hν U hUo hcl hbd
  have hD0 : 0 ≤ D := by linarith
  refine ⟨6 * Real.exp K * D ^ 3, c, 6, ?_, hc, ?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos K).le) (pow_nonneg hD0 3)
  intro k hk j p hp
  -- smoothness of the exponent `f_j = sq2(x_j)/(4a)` on `U`
  have hfcd : ContDiffOn ℝ 3 (fun q : Chart => sq2 (xj ν j q.2) / (4 * ageA ν q.1)) U := by
    have hg : ContDiff ℝ 3 (fun q : Chart => sq2 (xj ν j q.2)) := by
      unfold sq2 xj
      fun_prop
    have hden : ContDiff ℝ 3 (fun q : Chart => 4 * ageA ν q.1) := by
      unfold ageA
      fun_prop
    have hdivS : ContDiffOn ℝ 3 (fun q : Chart => sq2 (xj ν j q.2) / (4 * ageA ν q.1))
        {q : Chart | 0 < q.1} :=
      ContDiffOn.div hg.contDiffOn hden.contDiffOn
        (fun q hq => mul_ne_zero (by norm_num) (psc2_ageA_ne ν hν q hq))
    exact hdivS.mono (fun q hq => hcl (subset_closure hq))
  -- lower bound `T_j` and jet bound `D_j`
  have hT : ∀ q ∈ U, c * (j : ℝ) ^ 2 - K ≤ sq2 (xj ν j q.2) / (4 * ageA ν q.1) :=
    fun q hq => hlow j q hq
  have hDf : ∀ q ∈ U, ∀ i : ℕ, 1 ≤ i → i ≤ 3 →
      ‖iteratedFDerivWithin ℝ i (fun q : Chart => sq2 (xj ν j q.2) / (4 * ageA ν q.1)) U q‖
        ≤ (D * (1 + |(j : ℝ)|) ^ 2) ^ i :=
    fun q hq i h1 h3 => hjet j q hq i h1 h3
  have hx : 1 ≤ (1 + |(j : ℝ)|) ^ 2 := by nlinarith [abs_nonneg (j : ℝ)]
  have hDj1 : 1 ≤ D * (1 + |(j : ℝ)|) ^ 2 := one_le_mul_of_one_le_of_one_le hD1 hx
  have hDj0 : 0 ≤ D * (1 + |(j : ℝ)|) ^ 2 := by linarith
  have key := expNegCompJets hUo _ hfcd (c * (j : ℝ) ^ 2 - K) (D * (1 + |(j : ℝ)|) ^ 2)
    hDj1 hT hDf
  -- rewrite `exp(-(sq2)/(4a))` as `exp(-(sq2/(4a)))`
  have hfun : (fun q : Chart => Real.exp (-(sq2 (xj ν j q.2)) / (4 * ageA ν q.1)))
      = (fun q : Chart => Real.exp (-(sq2 (xj ν j q.2) / (4 * ageA ν q.1)))) := by
    funext q
    rw [neg_div]
  rw [hfun]
  have hkey := key k hk p hp
  have hexp : Real.exp (-(c * (j : ℝ) ^ 2 - K)) = Real.exp (-c * (j : ℝ) ^ 2) * Real.exp K := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfac : (k.factorial : ℝ) ≤ 6 := by
    interval_cases k <;> norm_num [Nat.factorial]
  have hDk : (D * (1 + |(j : ℝ)|) ^ 2) ^ k ≤ (D * (1 + |(j : ℝ)|) ^ 2) ^ 3 :=
    pow_le_pow_right₀ hDj1 hk
  have hdpos : 0 ≤ (D * (1 + |(j : ℝ)|) ^ 2) ^ k := pow_nonneg hDj0 k
  refine hkey.trans ?_
  rw [hexp]
  calc (k.factorial : ℝ) * (Real.exp (-c * (j : ℝ) ^ 2) * Real.exp K)
        * (D * (1 + |(j : ℝ)|) ^ 2) ^ k
      ≤ 6 * (Real.exp (-c * (j : ℝ) ^ 2) * Real.exp K) * (D * (1 + |(j : ℝ)|) ^ 2) ^ 3 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hfac (by positivity)) hDk hdpos (by positivity)
    _ = 6 * Real.exp K * D ^ 3 * (1 + |(j : ℝ)|) ^ 6 * Real.exp (-c * (j : ℝ) ^ 2) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
