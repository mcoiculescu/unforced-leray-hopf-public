import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1_3

/-!
# `PartIII-b:C/grad/3/5/1/3` D3d: absorbing the physical Gaussian into `hpAGauss`

Source `shorter-proof-2026-11-02.tex` 4963-4980, 5063-5079. Since `a = 1 + ν s ≤ 1 + ν s1` on
`0 ≤ s ≤ s1`, the Gaussian `exp(-y²/(4a))` of the physical term is dominated by
`exp(-y²/(4(1+ν s1)))`, which is the Gaussian weight of `hpAGauss`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hpA_gauss_absorb (ν s s1 : ℝ) (hν : 0 < ν) (hs : 0 ≤ s) (hss1 : s ≤ s1) (c : ℝ)
    (j : ℤ) (t : ℝ) :
    (1 + |t - (j : ℝ) * c|) ^ 5 * Real.exp (-(t - (j : ℝ) * c) ^ 2 / (4 * ageA ν s))
      ≤ hpAGauss (1 / (4 * (1 + ν * s1))) c j t := by
  unfold hpAGauss
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have ha : 0 < ageA ν s := by unfold ageA; positivity
  have hle : ageA ν s ≤ 1 + ν * s1 := by unfold ageA; nlinarith
  have hpos : 0 < 4 * ageA ν s := by linarith
  have hy : 0 ≤ (t - (j : ℝ) * c) ^ 2 := sq_nonneg _
  have h1 : (t - (j : ℝ) * c) ^ 2 / (4 * (1 + ν * s1)) ≤ (t - (j : ℝ) * c) ^ 2 / (4 * ageA ν s) :=
    div_le_div_of_nonneg_left hy hpos (by linarith)
  have h2 : (1 / (4 * (1 + ν * s1))) * (t - (j : ℝ) * c) ^ 2
      = (t - (j : ℝ) * c) ^ 2 / (4 * (1 + ν * s1)) := by
    ring
  have h3 : -(t - (j : ℝ) * c) ^ 2 / (4 * ageA ν s) = -((t - (j : ℝ) * c) ^ 2 / (4 * ageA ν s)) := by
    ring
  rw [h3, neg_mul, h2]
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
