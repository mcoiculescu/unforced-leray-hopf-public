import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.Targets

/-!
# `C/ret/8`: linearity of `e_A` in `A`

Source 4971-4972 (`e_A = Σ_j [2 B V_j + 2ν A^y : D²V_j - (A^y + (A^y)ᵀ) ∇p_j]`) and 4985.
`A^y` depends linearly on `A` pointwise, `B` by hypothesis, and the Hessian contraction and the
symmetrised matrix are linear in the matrix argument.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem eALinear : EALinear := by
  intro ν μ χ A A' r s x hB hB2 hS hS'
  have hAyAdd : Ay ν χ (A + A') s = Ay ν χ A s + Ay ν χ A' s := by
    simp only [Ay, Pi.add_apply, smul_add]
  have hAyR : Ay ν χ (r • A) s = r • Ay ν χ A s := by
    simp only [Ay, Pi.smul_apply]
    exact smul_comm _ _ _
  have hmvAdd : ∀ (M M' : Mat3) (v : Vec3), mv (M + M') v = mv M v + mv M' v := by
    intro M M' v
    funext i
    simp only [mv, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hmvSmul : ∀ (c : ℝ) (M : Mat3) (v : Vec3), mv (c • M) v = c • mv M v := by
    intro c M v
    funext i
    simp only [mv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hsymAdd : ∀ (M M' : Mat3) (v : Vec3),
      mv (fun a b => (M + M') a b + (M + M') b a) v
        = mv (fun a b => M a b + M b a) v + mv (fun a b => M' a b + M' b a) v := by
    intro M M' v
    funext i
    simp only [mv, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hsymSmul : ∀ (c : ℝ) (M : Mat3) (v : Vec3),
      mv (fun a b => (c • M) a b + (c • M) b a) v
        = c • mv (fun a b => M a b + M b a) v := by
    intro c M v
    funext i
    simp only [mv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hembAdd : ∀ u w : ℝ × ℝ, emb (u + w) = emb u + emb w := by
    intro u w
    funext i
    fin_cases i <;> simp [emb]
  have hembSmul : ∀ (c : ℝ) (u : ℝ × ℝ), emb (c • u) = c • emb u := by
    intro c u
    funext i
    fin_cases i <;> simp [emb]
  have hHAdd : ∀ (M M' : Mat3) (V : ℝ × ℝ → ℝ × ℝ) (y : ℝ × ℝ),
      hessContr (M + M') V y = hessContr M V y + hessContr M' V y := by
    intro M M' V y
    simp only [hessContr, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    rw [hembAdd]
  have hHSmul : ∀ (c : ℝ) (M : Mat3) (V : ℝ × ℝ → ℝ × ℝ) (y : ℝ × ℝ),
      hessContr (c • M) V y = c • hessContr M V y := by
    intro c M V y
    simp only [hessContr, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [hembSmul]
  have hT : ∀ j : ℤ, eATerm ν μ χ (A + A') s x j
      = eATerm ν μ χ A s x j + eATerm ν μ χ A' s x j := by
    intro j
    unfold eATerm
    rw [hB, hAyAdd, hHAdd, hsymAdd, hmvAdd]
    module
  have hTs : ∀ j : ℤ, eATerm ν μ χ (r • A) s x j = r • eATerm ν μ χ A s x j := by
    intro j
    unfold eATerm
    rw [hB2, hAyR, hHSmul, hsymSmul, hmvSmul]
    module
  constructor
  · simp only [eA_eq]
    rw [tsum_congr hT, Summable.tsum_add hS hS']
  · simp only [eA_eq]
    rw [tsum_congr hTs, tsum_const_smul'']

end UnforcedLeray.Short.PartIIIb.Concrete
