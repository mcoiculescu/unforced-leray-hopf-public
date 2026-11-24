import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.Targets

/-!
# `C/ret/7`: linearity of `f_A` in `A`

Source 4970 (`f_A = -Σ_j [(B_mer x_j)·∇V_j + B V_j]`) and 4985 (linear dependence on `A`).
The matrix `B` enters each lattice term linearly; `fA` is the negated `tsum` of the terms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fALinear : FALinear := by
  intro ν μ χ A A' r s x hB hB2 hS hS'
  have hmerAdd : ∀ (M M' : Mat3) (y : ℝ × ℝ),
      merApply (M + M') y = merApply M y + merApply M' y := by
    intro M M' y
    refine Prod.ext ?_ ?_ <;> simp only [merApply, Pi.add_apply, Prod.fst_add, Prod.snd_add] <;> ring
  have hmerSmul : ∀ (c : ℝ) (M : Mat3) (y : ℝ × ℝ),
      merApply (c • M) y = c • merApply M y := by
    intro c M y
    refine Prod.ext ?_ ?_ <;>
      simp only [merApply, Pi.smul_apply, smul_eq_mul, Prod.smul_fst, Prod.smul_snd] <;> ring
  have hmvAdd : ∀ (M M' : Mat3) (v : Vec3), mv (M + M') v = mv M v + mv M' v := by
    intro M M' v
    funext i
    simp only [mv, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hmvSmul : ∀ (c : ℝ) (M : Mat3) (v : Vec3), mv (c • M) v = c • mv M v := by
    intro c M v
    funext i
    simp only [mv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hembAdd : ∀ u w : ℝ × ℝ, emb (u + w) = emb u + emb w := by
    intro u w
    funext i
    fin_cases i <;> simp [emb]
  have hembSmul : ∀ (c : ℝ) (u : ℝ × ℝ), emb (c • u) = c • emb u := by
    intro c u
    funext i
    fin_cases i <;> simp [emb]
  have hT : ∀ j : ℤ, fATerm ν μ χ (A + A') s x j
      = fATerm ν μ χ A s x j + fATerm ν μ χ A' s x j := by
    intro j
    unfold fATerm
    rw [hB]
    simp only [hmerAdd, map_add, hembAdd, hmvAdd]
    abel
  have hTs : ∀ j : ℤ, fATerm ν μ χ (r • A) s x j = r • fATerm ν μ χ A s x j := by
    intro j
    unfold fATerm
    rw [hB2]
    simp only [hmerSmul, map_smul, hembSmul, hmvSmul, smul_add]
  constructor
  · simp only [fA_eq]
    rw [tsum_congr hT, Summable.tsum_add hS hS', neg_add]
  · simp only [fA_eq]
    rw [tsum_congr hTs, tsum_const_smul'', smul_neg]

end UnforcedLeray.Short.PartIIIb.Concrete
